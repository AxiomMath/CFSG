module

public import CFSG.LieType.Steinberg.TwistedE6.Transpose
public import CFSG.LieType.Steinberg.Minuscule.Cert
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

@[expose] def pCode : ℕ := 830824853133992554909121740929923116875587724206826890974082358

@[expose] def epsMask : ℕ := 10284379773341968512

@[expose] def rhoPos : List ℕ := [
  5, 1, 4, 3, 2, 0, 16, 15, 8, 9, 14, 13, 12, 11, 10, 7, 6, 26, 25, 19, 21, 20, 24, 23, 22, 18,
  17, 36, 33, 35, 31, 30, 32, 28, 34, 29, 27, 42, 45, 44, 40, 41, 37, 43, 39, 38, 51, 47, 52, 49,
  50, 46, 48, 57, 54, 58, 56, 53, 55, 63, 60, 62, 61, 59, 65, 64, 66, 67, 68, 69, 70, 71]

@[expose] def epsBit (k : ℕ) : Bool := epsMask / 2 ^ k % 2 == 1

@[expose] def rhoIdx (k : ℕ) : ℕ := rhoPos.getD k 0

@[expose] def conjOp (k : ℕ) : ℕ :=
  comp e6Data.d (comp e6Data.d (inv e6Data.d pCode) (e6Data.op (rhoIdx k))) pCode

@[expose] def twistedOp (k : ℕ) : ℕ := if epsBit k then conjOp k else neg e6Data.d (conjOp k)

@[expose] def checkPerm : Bool :=
  ((List.range e6Data.d).all fun a =>
      decide (2 ≤ dig pCode a) && decide (dig pCode a / 2 - 1 < e6Data.d)) &&
    (List.range e6Data.d).all fun a => (List.range e6Data.d).all fun b =>
      dig pCode a / 2 != dig pCode b / 2 || a == b

@[expose] def checkRho : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    decide (rhoIdx k < (Tag.rootCertificate .E6).roots.length) &&
      List.ofFn ((Tag.rootCertificate .E6).root (rhoIdx k)) ==
        List.ofFn (permLattice TwistTag.E6.perm ((Tag.rootCertificate .E6).root k))

@[expose] def checkTranspose : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    trCheck e6Data.d (e6Data.op k) (twistedOp k)

@[expose] def checkSimple : Bool :=
  (List.finRange 6).all fun i => !epsBit i && !epsBit ((Tag.rootCertificate .E6).image i i)

end CFSG.LieType.Steinberg.TwistedE6
