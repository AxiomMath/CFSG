module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section FieldAut

variable {K F : Type*} [Field K] [Field F]

theorem fieldAut_mem_projUnitriangular {n : ℕ} (σ : F ≃+* F) {u : projectiveSL n F}
    (hu : u ∈ projUnitriangular n F) : fieldAut n F σ u ∈ projUnitriangular n F := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [fieldAut_proj]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hU
  refine mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hlow i j hij, map_zero]
  · rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hdiag i,
      map_one]

theorem fieldAut_mem_inf_centralizer {n : ℕ} (σ : F ≃+* F) {y u : projectiveSL n F}
    (hy : fieldAut n F σ y = y)
    (hu : u ∈ projUnitriangular n F ⊓ centralizer ({y} : Set (projectiveSL n F))) :
    fieldAut n F σ u ∈ projUnitriangular n F ⊓ centralizer ({y} : Set (projectiveSL n F)) := by
  obtain ⟨hU, hC⟩ := mem_inf.1 hu
  refine mem_inf.2 ⟨fieldAut_mem_projUnitriangular σ hU, mem_centralizer_singleton_iff.2 ?_⟩
  have h := mem_centralizer_singleton_iff.1 hC
  have h1 := congrArg (fieldAut n F σ) h
  rw [map_mul, map_mul, hy] at h1
  exact h1

end FieldAut

section Four

variable {K F : Type*} [Field K] [Field F] [Finite F] [CharP F 2]

theorem exists_conj_eq_projMap_of_mul_self_of_fieldAut (hF : Nat.card F = 4) (ι : K →+* F)
    {z : projectiveSL 4 F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ (c : projectiveSL 4 F) (z₀ : projectiveSL 4 K) (R : Subgroup (projectiveSL 4 F)),
      c * z * c⁻¹ = projMap 4 ι z₀ ∧ R ≤ centralizer ({projMap 4 ι z₀} : Set _) ∧
        IsPGroup 2 R ∧ 2 ^ 10 ≤ Nat.card R ∧
        ∀ σ : F ≃+* F, (∀ a, σ (ι a) = ι a) → ∀ r ∈ R, fieldAut 4 F σ r ∈ R := by
  obtain ⟨hU2, hUc⟩ := isPGroup_projUnitriangular_four (F := F) hF
  obtain ⟨k, P, c₁, hc₁⟩ := exists_conj_eq_elt hz
  have hk : k ≤ 2 := by
    have h := Fintype.card_le_of_injective P.supp P.supp_injective
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  interval_cases k
  ·
    exfalso
    apply hz1
    rw [InvPlacement.elt, P.mat_eq_one_of_zero, map_one] at hc₁
    have h1 : z = c₁⁻¹ * (c₁ * z * c₁⁻¹) * c₁ := by group
    rw [h1, hc₁]
    group
  ·
    have hn : 2 ≤ 4 := by norm_num
    obtain ⟨c₂, hc₂⟩ := exists_conj_xab_eq_xab (K := F) (P.u_ne_w 0 0) (firstIdx_ne_lastIdx hn) 1
    have hP : P.elt F = xab (P.u_ne_w 0 0) 1 := by
      rw [InvPlacement.elt, P.mat_eq_transvection]
      rfl
    refine ⟨c₂ * c₁, xab (K := K) (firstIdx_ne_lastIdx hn) 1, projUnitriangular 4 F, ?_, ?_,
      hU2, ?_, fun σ _ r hr => fieldAut_mem_projUnitriangular σ hr⟩
    · rw [projMap_xab_one, ← hc₂, ← hP, ← hc₁]
      group
    · intro u hu
      rw [projMap_xab_one, mem_centralizer_singleton_iff]
      exact xab_first_last_mul_comm hn 1 hu
    · rw [hUc]
      norm_num
  ·
    refine ⟨proj 4 F (permSL P.permFour) * c₁, yTwo K,
      projUnitriangular 4 F ⊓ centralizer ({yTwo F} : Set (projectiveSL 4 F)), ?_, ?_, ?_, ?_,
      fun σ hσ r hr => ?_⟩
    · rw [projMap_yTwo, ← P.conj_elt_eq_yTwo, ← hc₁]
      group
    · rw [projMap_yTwo]
      exact inf_le_right
    · exact hU2.to_le inf_le_left
    · have h := card_pow_five_le_card_inf_centralizer_yTwo (F := F)
      rw [hF] at h
      calc 2 ^ 10 = 4 ^ 5 := by norm_num
        _ ≤ _ := h
    · have hy : fieldAut 4 F σ (yTwo F) = yTwo F := by
        rw [← projMap_yTwo ι, fieldAut_projMap ι hσ]
      exact fieldAut_mem_inf_centralizer σ hy hr

end Four

end CFSG.SeitzReduction.LinearPilot
