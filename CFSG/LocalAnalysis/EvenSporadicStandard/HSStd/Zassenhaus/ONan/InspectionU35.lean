module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionCommon
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
import CFSG.Quasithin.H13.NQCatA314SL3
import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
import CFSG.GH74.KGroups.L3EpsUniInv

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem card_projectiveSpecialLinearGroup_two_of_card_eq_five {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 60 := by
  rw [CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_projective_two_field F, hF]
  norm_num

theorem exists_subgroup_card_sixty_of_outer_involution {N : Type} [Group N]
    (hN : LieModel N .PSU 3 5 1) {σ : MulAut N} (hσ : σ * σ = 1) (hout : σ ∉ inner N) :
    ∃ M : Subgroup N, Nat.card M = 60 ∧ ∀ x y : N, σ x = x → σ y = y → ⁅x, y⁆ ∈ M := by
  have hSt : CFSG.Open.StatedClassicalModel N .PSU 3 5 1 :=
    LieModel.statedClassicalModel hN (by decide)
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hSt
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 5 1 F :=
    ⟨by norm_num, le_refl 1, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨θ, hθ⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_cover_of_equiv hU e₀
  obtain ⟨M, hGD, ⟨eM⟩⟩ :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3.graphData_of_cover_psl2 hU
      (by norm_num) (by norm_num) (by decide) hθ hσ hout
  refine ⟨M, ?_, fun x y hx hy => hGD.commutator_mem x y hx hy⟩
  rw [Nat.card_congr eM.toEquiv]
  exact card_projectiveSpecialLinearGroup_two_of_card_eq_five (F := ↥hU.fixedField)
    (by rw [hU.card_fixedField]; norm_num)

theorem commutator_subgroupOf_eq_self_of_le {Y : Type*} [Group Y] {N A : Subgroup Y} (hAN : A ≤ N)
    (hA : ⁅A, A⁆ = A) : ⁅A.subgroupOf N, A.subgroupOf N⁆ = A.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAN, hA]

theorem false_of_perfect_le_centralizer_psu_three_five {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSU 3 5 1) {z : N} (hz : orderOf z = 2) {A : Subgroup N}
    (hAz : A ≤ centralizer ({z} : Set N)) (hperf : ⁅A, A⁆ = A) (hcard : Nat.card A = 360) :
    False := by
  have hSt : CFSG.Open.StatedClassicalModel N .PSU 3 5 1 :=
    LieModel.statedClassicalModel hN (by decide)
  have h120 := CFSG.Quasithin.H13.NQCat.A314D.cent_sl3five (X := N) ⟨false, Or.inl hSt⟩ z hz
  have hle : Nat.card A ≤ Nat.card ↥⁅centralizer ({z} : Set N), centralizer ({z} : Set N)⁆ :=
    Subgroup.card_le_of_le (by rw [← hperf]; exact Subgroup.commutator_mono hAz hAz)
  omega

theorem false_of_perfect_le_fixed_psu_three_five {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSU 3 5 1) {σ : MulAut N} (hσ : σ * σ = 1) (hout : σ ∉ inner N)
    {A : Subgroup N} (hAσ : ∀ a ∈ A, σ a = a) (hperf : ⁅A, A⁆ = A) (hcard : Nat.card A = 360) :
    False := by
  obtain ⟨M, hM60, hMcomm⟩ := exists_subgroup_card_sixty_of_outer_involution hN hσ hout
  have hAM : A ≤ M := by
    rw [← hperf]
    exact Subgroup.commutator_le.2 fun a ha b hb => hMcomm a b (hAσ a ha) (hAσ b hb)
  have hle : Nat.card A ≤ Nat.card M := Subgroup.card_le_of_le hAM
  omega

theorem inspectionArm_psu_three_five : InspectionArm fun N _ => LieModel N .PSU 3 5 1 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_lieModel_psu_three_five hQ
  have hidx : N.index ≤ 6 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_lieModel_psu_three_five hQ)
  obtain ⟨w, hw2, H, A, hH, hwH, _, _, hAH, hAN, hA, _, hperf, _⟩ :=
    exists_simple_le_of_pgl29 (N := N) (by omega) hw
  have hAcard : Nat.card (A.subgroupOf N) = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA]
  have hAperf : ⁅A.subgroupOf N, A.subgroupOf N⁆ = A.subgroupOf N :=
    commutator_subgroupOf_eq_self_of_le hAN hperf
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · refine false_of_perfect_le_centralizer_psu_three_five hQ (z := ⟨w, hwN⟩) ?_
      (A := A.subgroupOf N) ?_ hAperf hAcard
    · rw [Subgroup.orderOf_mk, hw2]
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hxw : (x : Y) ∈ centralizer ({w} : Set Y) := hAw hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxw
      simpa using hxw
  · set σ : MulAut ↥N := MulAut.conjNormal w with hσdef
    have hσ : σ * σ = 1 := by
      have hord := orderOf_conjNormal_eq_two hC hw2 hwN
      rw [hσdef, ← pow_two, ← hord, pow_orderOf_eq_one]
    have hout : σ ∉ inner ↥N := by
      rw [hσdef]
      exact conjNormal_not_mem_inner hC hwN
    have hAσ : ∀ a ∈ A.subgroupOf N, σ a = a := by
      intro a ha
      apply Subtype.ext
      rw [hσdef, MulAut.conjNormal_apply]
      have haw : w * (a : Y) = (a : Y) * w :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hAw ha)).symm
      rw [haw]
      group
    exact false_of_perfect_le_fixed_psu_three_five hQ hσ hout (A := A.subgroupOf N) hAσ hAperf
      hAcard

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
