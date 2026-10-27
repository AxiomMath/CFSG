module

public import Certificates.Certificate3008

public section

namespace CFSG.EvenSmallLie.SympSix

open CFSG.LieType.Multipliers CFSG.CosetTable

theorem model_check :
    ((rels.all fun r => decide (wordPerm r = 1)) &&
      ((List.finRange 3).all fun i => decide (wordPerm (commWords (coverPairs i)) = sympGen i)) &&
      decide (wordPerm wordSB = CFSG.EvenSmallLie.Sp6.sp6B)) = true :=
  Certificates.certificate3008.1

theorem pres_check :
    (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
      (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56 :=
  Certificates.certificate3008.2.1

theorem presY_check :
    (Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
        (FreeGroup.mk [(1, true)]))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
        (FreeGroup.mk [(1, true)]))).index ≤ 5184 :=
  Certificates.certificate3008.2.2.1

theorem cover_check :
    (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
      (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56 :=
  Certificates.certificate3008.2.2.2.1

theorem cover₁_check :
    Finite (PG _ cover₁) ∧ Nat.card (PG _ cover₁) ≤ 51840 :=
  Certificates.certificate3008.2.2.2.2

end CFSG.EvenSmallLie.SympSix
