module

public import CFSG.RankThree.PartOne.KS.J2FiveData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ComponentClassification.AS81.Sec2

open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

@[expose] def j2NormD2 (k : ℕ) : Array ℕ := (j2FiveDGenArrs[2]!)[k]!

@[expose] def j2NormD5 (k : ℕ) : Array ℕ := (j2FiveDGenArrs[5]!)[k]!

@[expose] def j2NormX (i : ℕ) : Array ℕ := j2FiveLineArrs[i]!

@[expose] def j2NormT2 : Array ℕ :=
  compA 315 (compA 315 (compA 315 (j2NormD2 0) (j2NormD2 2)) (j2NormD2 1)) (j2NormD2 1)

@[expose] def j2NormT5 : Array ℕ :=
  compA 315 (compA 315 (compA 315 (compA 315 (j2NormD5 0) (j2NormD5 1)) (j2NormD5 0))
    (j2NormD5 1)) (j2NormD5 1)

@[expose] def j2NormC : Array ℕ := compA 315 j2NormT2 j2NormT5

@[expose] def j2NormB : Array ℕ :=
  compA 315 (compA 315 j2NormC (j2NormX 0)) (invCand 315 j2NormC)

@[expose] def j2NormCheck : Bool :=
  validA 315 (j2NormD2 0) && validA 315 (j2NormD2 1) && validA 315 (j2NormD2 2) &&
    validA 315 (j2NormD5 0) && validA 315 (j2NormD5 1) && validA 315 j2NormC &&
    eqA 315 j2NormB (compA 315 (j2NormX 1) (compA 315 (j2NormX 1) (j2NormX 1))) &&
    eqA 315 (compA 315 (j2NormX 0) (j2NormX 1)) (compA 315 (j2NormX 1) (j2NormX 0)) &&
    eqA 315 (compA 315 (compA 315 (compA 315 j2NormC j2NormB) (invCand 315 j2NormC))
      (compA 315 (j2NormX 0) j2NormB)) (idA 315)

end CFSG.ComponentClassification.AS81.Sec2
