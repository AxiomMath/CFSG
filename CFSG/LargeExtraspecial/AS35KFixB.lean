module

public import CFSG.LargeExtraspecial.AS35KFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35K

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.AxisFlag
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {A : GL (Fin m) K} {φ : K ≃+* K}

theorem exists_add_frob_eq {b : K} (hb : b = 0 ∨ b = 1) : ∃ c : K, c + frob c = b := by
  rcases hb with rfl | rfl
  · exact ⟨0, by rw [map_zero, add_zero]⟩
  · exact ⟨ω, omega_add_frob⟩

theorem semi_e (hm : 3 ≤ m) {e f : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    (hef : herm frob e f = 1)
    (hcomm : ∀ a ∈ Rhat m e, ∀ x, semi A φ (a • x) = a • semi A φ x) :
    semi A φ e = herm frob e (semi A φ f) • e := by
  have h := hcomm (tvU e) (tvU_mem_Rhat hm he0 he) f
  rw [tvU_smul he, tvU_smul he, hef, one_smul, semi_add] at h
  exact add_left_cancel h

theorem semi_flag (hm : 3 ≤ m) {e f u : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    (hef : herm frob e f = 1) (heu : herm frob e u = 0) {c : K}
    (hc : c + frob c = herm frob u u)
    (hcomm : ∀ a ∈ Rhat m e, ∀ x, semi A φ (a • x) = a • semi A φ x) :
    semi A φ u = herm frob e (semi A φ f) • u +
      (herm frob u (semi A φ f) + c * herm frob e (semi A φ f) -
        φ (herm frob u f + c) * herm frob e (semi A φ f)) • e := by
  obtain ⟨a, ha, hax⟩ := exists_flag_mem_Rhat hm he0 he heu hc
  have h := hcomm a ha f
  have hSe := semi_e hm he0 he hef hcomm
  rw [hax, hax, hef, mul_one, one_smul, semi_add, semi_add, semi_smul, hSe, smul_smul] at h
  linear_combination (norm := module) h

theorem exists_flag_data (hm : 4 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    ∃ f : Fin m → K, herm frob f f = 0 ∧ herm frob e f = 1 ∧
      ∃ w : Fin m → K, herm frob e w = 0 ∧ herm frob f w = 0 ∧ w ≠ 0 ∧
        ∀ α β : K, α • w = β • e → α = 0 := by
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨⟨f, hff, hef⟩, -, -, -, -, -, -, -, -, -, -, hrest⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  obtain ⟨hcompl, hfin, -⟩ := hrest f hff hef
  rw [Module.finrank_fin_fun] at hfin
  obtain ⟨w, hwD, hw0⟩ : ∃ w ∈ partnerPerp (AS35U.hermB m) e f, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : partnerPerp (AS35U.hermB m) e f = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Submodule.mem_bot K).mpr (hcon x hx)
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨hew, hfw⟩ := mem_partnerPerp.mp hwD
  refine ⟨f, hff, hef, w, hew, hfw, hw0, fun α β h => ?_⟩
  by_contra hα
  apply hw0
  have hw : w = (α⁻¹ * β) • e := by rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hspan : w ∈ Submodule.span K {e, f} := by
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have := hcompl.inf_eq_bot
  have hmem : w ∈ Submodule.span K {e, f} ⊓ partnerPerp (AS35U.hermB m) e f := ⟨hspan, hwD⟩
  rw [this] at hmem
  exact (Submodule.mem_bot K).mp hmem

theorem phi_eq (hm : 4 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    (hcomm : ∀ a ∈ Rhat m e, ∀ x, semi A φ (a • x) = a • semi A φ x) (μ : K) : φ μ = μ := by
  have hm3 : 3 ≤ m := by omega
  obtain ⟨f, -, hef, w, hew, -, -, hind⟩ := exists_flag_data hm he0 he
  set l := herm frob e (semi A φ f) with hl
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := semi_e hm3 he0 he hef hcomm
    rw [← hl, h0, zero_smul] at h1
    exact semi_ne_zero A φ he0 h1
  obtain ⟨c₁, hc₁⟩ := exists_add_frob_eq (herm_self_eq_zero_or_one w)
  obtain ⟨c₂, hc₂⟩ := exists_add_frob_eq (herm_self_eq_zero_or_one (μ • w))
  have hemw : herm frob e (μ • w) = 0 := by rw [herm_smul_right, hew, mul_zero]
  have h1 := semi_flag hm3 he0 he hef hew hc₁ hcomm
  have h2 := semi_flag hm3 he0 he hef hemw hc₂ hcomm
  rw [semi_smul, h1, ← hl] at h2
  have h3 : (φ μ * l - l * μ) • w =
      ((herm frob (μ • w) (semi A φ f) + c₂ * l - φ (herm frob (μ • w) f + c₂) * l) -
        φ μ * (herm frob w (semi A φ f) + c₁ * l - φ (herm frob w f + c₁) * l)) • e := by
    linear_combination (norm := module) h2
  have h4 := hind _ _ h3
  have h5 : (φ μ - μ) * l = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h5 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hl0

end CFSG.LargeExtraspecial.AS35K
