# -*- encoding: utf-8 -*-
u"""
加法準同型暗号

0/1特徴量の束で表現されたデータベースがあるとする。

クライアントはサーバが持っているデータベースに類似のレコードが何件あるかを知りたい。
しかし検索クエリーをサーバに教えたくない。そこで暗号化する。

>>> seed(12345)
>>> c.make_query('11000')
[(125, 1638), (1324, 1211), (2162, 2120), (1021, 61), (93, 528)]

暗号化したクエリと、類似度のしきい値(今回は2/3)をサーバに送ると、
サーバは *暗号化したまま* 自分の持っている各データとの類似度を計算して返す。

>>> query = _
>>> Server.search(query, 2, 3)
[(1567, 51), (592, 1161), (2076, 179), (1136, 1545), (254, 12), (1147, 1288)]

クライアントはこれを復号する。今回2309を法として計算しているので2304は-5という意味になる。
非負の値のものが、しきい値以上に類似していたものになる。
今回は3件類似のデータがあることがわかる。

>>> response = _
>>> print [c.decode(x) for x in response]
[-4, -2, 0, 2, -1, 0]


FAQ

Q: どうして暗号化したまま計算できるのか？
A: 暗号化した世界でのある演算(下記add関数)と暗号化してない世界の足し算が同じ構造をしている(準同型)から

>>> c.decode(add(c.encode(123, random()), c.encode(234, random())))
357

Q: 1と0を個別に暗号化するのではバレバレでは？
A: 暗号化の際に乱数を振っているので同じ値を暗号化しても異なる値になる。復号の際にはこの乱数が必要ない仕組みになっている。

>>> c.encode(1, random_u=123)
(914, 2032)
>>> c.encode(1, random_u=234)
(1480, 1454)
>>> c.decode((1480, 1454))
1

Q: 「足し算しか使ってない」と聞いたが掛け算も使っているように見える
A: 離散対数を使っている今回の実装ではスカラー倍が効率よく計算できる。
　 そうでない場合でも、整数倍の演算は足し算だけで(速度はさておき理論上は)計算できる。
"""

from random import seed

NUM_FEATURES = 5

def random():
    from random import random
    return int(random() * 1000)

## 剰余群の演算

def exponent(x, y, mod=None):
    """
    >>> exponent(2, 2, 5)
    4
    >>> exponent(2, 3, 5)
    3
    >>> exponent(2, 4, 5)
    1
    >>> exponent(2, -1, 5)
    3
    """
    if mod == None: mod = Shared.modulo
    if y < 0:
        y += mod - 1 # 下記invert参照
    bin = []
    while y > 0:
        bin.append(y % 2)
        y /= 2

    powers = [x]
    p = x
    for i in range(1, len(bin)):
        p = (p * p) % mod
        powers.append(p)

    result = 1
    for b, p in zip(bin, powers):
        if b:
            result = (result * p) % mod

    return result


def invert(x, mod=None):
    """
    逆元を求める。フェルマーの小定理より、
    素数 p の剰余群で x ** (p - 1) は単位元になる
    ので、x ** (p - 2) が n の逆元になる

    >>> invert(123, 2309)
    413
    >>> 123 * 413 % 2309
    1
    """
    if mod == None: mod = Shared.modulo
    return exponent(x, mod - 2, mod)


def mul(x, y, mod=None):
    if mod == None: mod = Shared.modulo
    return (x * y) % mod


def logarithm(n, p, mod=None):
    """
    n ** x = pとなるxを力づくで求める
    >>> logarithm(7, 1)
    0
    >>> logarithm(7, 7)
    1
    >>> logarithm(7, 7 ** 3)
    3
    >>> logarithm(2, invert(2))
    -1
    >>> logarithm(2, 3, mod=7)
    Traceback (most recent call last):
    ...
    RuntimeError: No solution
    """
    if mod == None: mod = Shared.modulo
    result = 0
    posi = nega = 1
    invn = invert(n, mod)
    while True:
        if posi == p:
            return result
        if nega == p:
            return -result

        result += 1
        posi = mul(posi, n, mod)
        nega = mul(nega, invn, mod)
        if posi == 1: raise RuntimeError('No solution')


## 暗号文の演算

def add(enc1, enc2):
    """
    >>> enc_2 = add(c.encode(1, 123), c.encode(1, 234))
    >>> c.decode(enc_2)
    2
    >>> c.decode(add(enc_2, enc_2))
    4
    >>> enc_1 = c.encode(1, 345)
    >>> c.decode(add(enc_2, enc_1))
    3
    """
    e1c1, e1c2 = enc1
    e2c1, e2c2 = enc2
    return (mul(e1c1, e2c1),
            mul(e1c2, e2c2))


def add_m(enc, a):
    """暗号文への暗号化されていない値の加算
    >>> one = c.encode(1, random())
    >>> c.decode(add_m(one, 123))
    124
    """
    c1, c2 = enc
    (f, g, h) = Shared.public
    return (c1, mul(c2, exponent(f, a)))


def negate(x):
    c1, c2 = x
    return (invert(c1), invert(c2))


def scalar(x, k):
    """スカラー倍
    >>> one = c.encode(1, random())
    >>> c.decode(scalar(one, 123))
    123
    """
    c1, c2 = x
    return (exponent(c1, k), exponent(c2, k))


def calc_p_size(p):
    """
    pの中の1の個数をpを暗号化したまま計算する

    >>> c.decode(calc_p_size(c.make_query('11111')))
    5
    >>> c.decode(calc_p_size(c.make_query('11011')))
    4
    >>> c.decode(calc_p_size(c.make_query('01010')))
    2
    >>> c.decode(calc_p_size(c.make_query('00000')))
    0
    """
    return reduce(add, p)


def calc_p_and_q(p, q):
    """
    pとqの両方のビットが立っている個数を数える
    >>> c.decode(calc_p_and_q(c.make_query('11100'), '11000'))
    2
    >>> c.decode(calc_p_and_q(c.make_query('11100'), '00110'))
    1
    >>> c.decode(calc_p_and_q(c.make_query('11100'), '00011'))
    0
    """
    result = (1, 1) # means zero: (g^0, h^0 * f^0)
    for pi, qi in zip(p, q):
        if qi == '1':
            result = add(result, pi)

    return result



## 登場人物

class Shared(object):
    "サーバとクライアントで共有している情報"
    modulo = 2309  # 適当な素数(2 * 3 * 5 * 7 * 11 - 1)
    public = None  # clientの初期化時に作る


class Client(object):
    def initialize(self, f, g, random_z):
        self.private = random_z
        h = exponent(g, random_z)
        Shared.public = (f, g, h)
        print "public key:", Shared.public

    def encode(self, m, random_u):
        (f, g, h) = Shared.public
        message = (
            exponent(g, random_u),
            mul(exponent(h, random_u), exponent(f, m)))
        return message

    def decode(self, message):
        (f, g, h) = Shared.public
        c1, c2 = message
        M = mul(c2, invert(exponent(c1, self.private)))
        return logarithm(f, M)

    def make_query(self, fv):
        """
        特徴ベクトルを暗号化されたクエリにする
        """
        assert isinstance(fv, str) and len(fv) == NUM_FEATURES
        result = []
        for c in fv:
            if c == '0':
                result.append(self.encode(0, random()))
            elif c == '1':
                result.append(self.encode(1, random()))
            else:
                raise AssertionError('not here')

        return result


class Server(object):
    secret_database = "11111 11110 11100 11000 10000 11010".split()

    @staticmethod
    def search(p, th_n, th_d, alpha=1, beta=1):
        """データベース内の各化合物ごとに暗号化されたまま類似度を計算する

        しきい値1/2だと1件だけアウト

        >>> ret = Server.search(c.make_query('11000'), 1, 2)
        >>> [c.decode(x) for x in ret]
        [-1, 0, 1, 2, 0, 1]

        しきい値7/8だと1件を除きアウト(セーフなのはベストマッチの化合物)

        >>> ret = Server.search(c.make_query('11000'), 7, 8)
        >>> [c.decode(x) for x in ret]
        [-19, -12, -5, 2, -6, -5]
        """
        result = []
        k1 = (alpha + beta - 1) * th_n + th_d
        k2 = th_n * alpha
        k3 = th_n * beta
        p_size = reduce(add, p)
        for q in Server.secret_database:
            q_size = q.count('1')
            tmp = scalar(calc_p_and_q(p, q), k1)
            tmp = add(tmp, scalar(p_size, -k2))
            tmp = add_m(tmp, -q_size * k3)
            result.append(tmp)

        return result # シャッフルしたりしても良い


def _test():
    import doctest
    doctest.testmod()


if __name__ == '__main__':
    seed(12345)
    c = Client()
    c.initialize(2, 3, 4)
    _test()
    print 'ok'
