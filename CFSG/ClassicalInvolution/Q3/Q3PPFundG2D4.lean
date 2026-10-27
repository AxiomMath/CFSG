module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSL3
import CFSG.ClassicalInvolution.AschTight.S19GD4Aut
import CFSG.ClassicalInvolution.AschTight.S19GG2Aut
import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
import CFSG.ClassicalInvolution.Asc77.AscMuTabTD4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

theorem eq_one_or_conj_of_inner_invol {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    {ρ : MulAut X} (hρ2 : ρ * ρ = 1) {g : X} (hg : ρ = MulAut.conj g) :
    ρ = 1 ∨ ∃ s : X, orderOf s = 2 ∧ ρ = MulAut.conj s := by
  have hgg : g * g = 1 := by
    have h : MulAut.conj (g * g) = 1 := by
      rw [map_mul, ← hg]
      exact hρ2
    exact (conj_eq_one_iff_of_center_eq_bot hZ _).mp h
  by_cases hg1 : g = 1
  · left
    rw [hg, hg1, map_one]
  · right
    exact ⟨g, orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1, hg⟩


theorem fixedOddFreeFund_g2 : FixedOddFreeFund (CompData.model .G2 0) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm : StatedLieAdmissible .G2 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩
  have hZ : Subgroup.center (CompData.model .G2 0).G = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0 le_rfl
  refine fixedOddFreeFund_of_center_eq_bot hZ ?_
  intro ρ hρ2 ⟨R, hR, hρR⟩
  obtain ⟨c, -, -, hc, -⟩ := MuTab.g2_exists_orderFour (p := 3) (e := 1) hp2 le_rfl hR
  obtain ⟨g, hg⟩ := S19G.exists_conj_of_fixes_g2 (p := 3) hp2 (e := 1) le_rfl ρ hR hρR
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc.sq) hc.ne_one
  exact oddCoreIn_fixed_eq_bot_of_model (t := .G2) (n := 0) trivial hadm
    (eq_one_or_conj_of_inner_invol hZ hρ2 hg) ⟨c, hc2⟩

theorem fixedOddFreeFund_trialityD4 : FixedOddFreeFund (CompData.model .trialityD4 0) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm : StatedLieAdmissible .trialityD4 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hZ : Subgroup.center (CompData.model .trialityD4 0).G = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 le_rfl
  refine fixedOddFreeFund_of_center_eq_bot hZ ?_
  intro ρ hρ2 ⟨R, hR, hρR⟩
  obtain ⟨c, -, -, hc, -⟩ := MuTab.td4_exists_orderFour (p := 3) (e := 1) hp2 hadm hR
  have hαn : ρ ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact hρ2
  obtain ⟨g, hg⟩ := S19G.exists_conj_of_fixes_d4 (p := 3) hp2 (e := 1) le_rfl ρ (n := 1) hαn hR hρR
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc.sq) hc.ne_one
  exact oddCoreIn_fixed_eq_bot_of_model (t := .trialityD4) (n := 0) trivial hadm
    (eq_one_or_conj_of_inner_invol hZ hρ2 hg) ⟨c, hc2⟩

end CFSG.ClassicalInvolution.Q3.Q3PP
