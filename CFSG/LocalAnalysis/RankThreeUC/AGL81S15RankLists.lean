module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def IsRankTwoPlus : TauCeti.LieTypeIndex → Prop
  | .A l Q => Q.p = 2 ∧ 2 ≤ l
  | .twistedA l Q => Q.p = 2 ∧ 3 ≤ l
  | .B l Q => Q.p = 2 ∧ 2 ≤ l
  | .D l Q => Q.p = 2 ∧ 4 ≤ l
  | .twistedD l Q => Q.p = 2 ∧ 4 ≤ l
  | .G2 Q => Q.p = 2
  | _ => False

@[expose] def RankOneList : TauCeti.LieTypeIndex → Prop
  | .A 2 Q => Odd Q.exponent
  | _ => False

@[expose] def RankTwoList : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | .B 2 _ => True
  | .A 2 Q => Even Q.exponent
  | .twistedA 2 Q => Odd Q.exponent
  | .A 3 Q => Odd Q.exponent
  | .twistedA 3 Q => Even Q.exponent
  | .A 4 Q => Odd Q.exponent
  | .twistedA 4 Q => Even Q.exponent
  | _ => False

@[expose] def RankThreeList : TauCeti.LieTypeIndex → Prop
  | .B 3 _ => True
  | .twistedD 4 _ => True
  | .A 3 Q => Even Q.exponent
  | .twistedA 3 Q => Odd Q.exponent
  | .A 5 Q => Odd Q.exponent
  | .twistedA 5 Q => Even Q.exponent
  | .A 6 Q => Odd Q.exponent
  | .twistedA 6 Q => Even Q.exponent
  | _ => False

@[expose] def In1512 : TauCeti.LieTypeIndex → Prop
  | .G2 Q => Q.p = 2
  | .A 2 Q => Q.p = 2
  | .A 3 Q => Q.p = 2
  | .twistedA 3 Q => Q.p = 2
  | .B 2 Q => Q.p = 2
  | .B 3 Q => Q.p = 2
  | .twistedD 4 Q => Q.p = 2
  | .A 4 Q => Q.card = 2
  | .A 5 Q => Q.card = 2
  | .A 6 Q => Q.card = 2
  | .twistedA 4 Q => Q.card = 4
  | _ => False

@[expose] def Rk3Cases (d : TauCeti.LieTypeIndex) (z : ℕ) : Prop :=
  (mRankChev d 3 z = 1 ↔ RankOneList d) ∧ (mRankChev d 3 z = 2 ↔ RankTwoList d) ∧
    (mRankChev d 3 z = 3 ↔ RankThreeList d) ∧
    (RankOneList d ∨ RankTwoList d ∨ RankThreeList d ∨ 4 ≤ mRankChev d 3 z)

end CFSG.LocalAnalysis.RankThreeUC.S15
