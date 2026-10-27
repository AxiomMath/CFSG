module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PCentralLayerGLA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.KGroupCarrier

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B.Pinned CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

section Table


theorem card_B_dvd_monsterOrder : Nat.card NativeSporadic.B ∣ monsterOrder := by
  rw [CFSG.RankThree.OddKernel.card_B_eq]
  unfold monsterOrder
  decide +kernel

theorem not_forty_one_dvd_card_B : ¬ 41 ∣ Nat.card NativeSporadic.B := by
  rw [CFSG.RankThree.OddKernel.card_B_eq]
  decide +kernel

theorem tabBFiveBNoComp_of_kGroup (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    (hB : CFSG.Open.IsKGroup NativeSporadic.B) : TabBFiveBNoComp := by
  intro J hJ
  have hfin : Finite NativeSporadic.B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hR := bFiveRel
  set C := Subgroup.centralizer ({zFive} : Set NativeSporadic.B) with hC
  have hPC : FiveLocal.P xFive qFive ≤ C := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hR.mem_H0.1 (hR.P_le_H0 hg)).2
  have hzC : zFive ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcent : ∀ g ∈ C, g * zFive = zFive * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hg zFive (Set.mem_singleton _)).symm
  have hCB : Nat.card C ∣ Nat.card NativeSporadic.B := Subgroup.card_subgroup_dvd_card C
  have h56 : 5 ^ 6 ∣ Nat.card C := hR.card_P ▸ Subgroup.card_dvd_of_le hPC
  have hfac : (Nat.card C).factorization 5 = 6 := by
    have hle1 : 6 ≤ (Nat.card C).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 h56
    have hle2 : (Nat.card C).factorization 5 ≤ (Nat.card NativeSporadic.B).factorization 5 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hCB 5
    rw [CFSG.RankThree.Native.factorization_card_B_five] at hle2
    omega
  have hP : Nat.card (FiveLocal.P xFive qFive) = 5 ^ (Nat.card C).factorization 5 := by
    rw [hfac]
    exact hR.card_P
  obtain ⟨K, hK, h5K⟩ := PCentralLayer.exists_component_dvd_card_center_of_glaPComponent
    Nat.prime_five hzC hcent hR.orderOf_z hPC hP
    (fun c hc hcomm => mem_zpowers_of_commute_P hR hc hcomm)
    gLAPPrimeCoreOf_centralizer_zFive_eq_bot hJ
  have hq : CFSG.Open.IsQuasisimple ↥K := ⟨hK.1.1.1, hK.1.2.1⟩
  have hKg : CFSG.Open.IsKGroup ↥K := (hB.subgroup C).subgroup K
  have hKB : Nat.card ↥K ∣ Nat.card NativeSporadic.B :=
    (Subgroup.card_subgroup_dvd_card K).trans hCB
  have h1341 := FiveCentralLeaf.five_central_leaf hGA hSpM hq hKg h5K
    (hKB.trans card_B_dvd_monsterOrder)
  exact not_forty_one_dvd_card_B
    ((Dvd.intro_left 13 rfl).trans (h1341.trans hKB))

end Table

section Consumer

set_option linter.unusedSectionVars false


theorem sporPair_B_five_of_tab'
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .B 5) (hChev : ChevStrong 5) (hHS : SporStrong .HS 5)
    (hA : TabBFiveACard) (hB : CFSG.Open.IsKGroup NativeSporadic.B → TabBFiveBNoComp) :
    SporPair .B 5 := by
  intro X _ _ hX K B hH hN hS hF hO
  exact sporPair_B_five_of_tab hOut hSpM hBr hP hChev hHS hA
    (hB (isKGroup_carrier_of_sporType hBr hX hS)) X hX K B hH hN hS hF hO

end Consumer

end CFSG.HardMathSupport.Dickson.I271
