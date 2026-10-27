module

public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Monster.Tri.GmatF1Type
public import CFSG.Monster.AxisCount.BabySetup
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.Existence CFSG.Monster.Generated CFSG.Monster.Visible

theorem card_isPGroup_seven_le_of_involution
    {w : Gmat} (hw : orderOf w = 2) {Q : Subgroup Gmat} (hQ : IsPGroup 7 Q)
    (hle : Q ≤ Subgroup.centralizer ({w} : Set Gmat)) : Nat.card Q ≤ 7 ^ 2 := by
  have hdvd := Subgroup.card_dvd_of_le hle
  refine card_le_of_isPGroup_of_dvd (by norm_num) hQ (n := Nat.card ↥(Subgroup.centralizer
    ({w} : Set Gmat))) (e := 2) ?_ hdvd
  rcases Census.generated_group_two_involution_classes w hw with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj]
    have hx : Nat.card ↥(Subgroup.centralizer ({xGmat} : Set Gmat)) = twoBCentralizerOrder := by
      have e1 : Subgroup.centralizer ({xGmat} : Set Gmat) = Gvis.subgroupOf Gmat :=
        Census.cent_xGmat_eq
      rw [e1, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (show Gvis ≤ Gmat from Hmat_le_Gmat)).toEquiv]
      exact natCard_Gvis
    rw [hx, twoBCentralizerOrder]
    norm_num
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj]
    have ht : Nat.card ↥(Subgroup.centralizer ({tGmat} : Set Gmat)) =
        11707448673375 * (2 ^ 24 * 42305421312000) := by
      rw [Nat.card_congr CFSG.Monster.Tri.centEquivCgen.toEquiv,
        CFSG.Monster.AxisCount.Baby.natCard_Cgen, CFSG.Monster.AxisCount.natCard_Jstar]
    rw [ht]
    norm_num

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
