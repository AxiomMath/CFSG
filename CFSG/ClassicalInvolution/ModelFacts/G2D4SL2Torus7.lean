module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix Polynomial
open scoped MatrixGroups

section Seven

variable {F : Type} [Field F]

theorem normTorus_prod_three_entries (κ u v : F) (h : u ^ 2 - κ * v ^ 2 = 1) (s₁ s₃ : Fˣ)
    (hrel : u ^ 2 * (((s₁ : F) + 1) * ((s₃ : F) + 1)) = 1) :
    (((normTorusSL κ s₁ u v h * normTorusSL κ 1 u v h * normTorusSL κ s₃ u v h : SL2 F)) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
    (((normTorusSL κ s₁ u v h * normTorusSL κ 1 u v h * normTorusSL κ s₃ u v h : SL2 F)) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = v * (1 - (s₁ : F) * (s₃ : F)) := by
  have hs₁0 : (s₁ : F) ≠ 0 := s₁.ne_zero
  have hs₃0 : (s₃ : F) ≠ 0 := s₃.ne_zero
  constructor
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_normTorusSL, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination (κ * v) * hrel - (κ * v) * h
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_normTorusSL, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination v * hrel - (v * (s₁ : F) * (s₃ : F)) * h

theorem exists_conic_point_seven [Finite F] (h7 : 7 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (κ : F) :
    ∃ u v : F, u ^ 2 - κ * v ^ 2 = 1 ∧ u ≠ 0 ∧ v ≠ 0 := by
  have hex : ∃ m : F, m * ((1 + κ * m ^ 2) * (1 - κ * m ^ 2)) ≠ 0 := by
    let f : F[X] := X * ((1 + C κ * X ^ 2) * (1 - C κ * X ^ 2))
    have hf : f ≠ 0 := by
      intro h
      have := congrArg (fun p => p.coeff 1) h
      simp [f] at this
    have hdeg : f.natDegree < Nat.card F := by
      have : f.natDegree ≤ 5 := by simp only [f]; compute_degree
      omega
    obtain ⟨m, hm⟩ := exists_eval_ne_zero_fin f hf hdeg
    exact ⟨m, by simpa [f] using hm⟩
  obtain ⟨m, hm⟩ := hex
  have hm0 : m ≠ 0 := left_ne_zero_of_mul hm
  have hmp : 1 + κ * m ^ 2 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hm)
  have hmm : 1 - κ * m ^ 2 ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hm)
  exact ⟨(1 + κ * m ^ 2) / (1 - κ * m ^ 2), 2 * m / (1 - κ * m ^ 2), conic_point κ m hmm,
    div_ne_zero hmp hmm, div_ne_zero (mul_ne_zero h2 hm0) hmm⟩

theorem exists_three_params [Finite F] (h7 : 7 ≤ Nat.card F) {u : F} (hu : u ≠ 0) :
    ∃ s₁ s₃ : Fˣ, u ^ 2 * (((s₁ : F) + 1) * ((s₃ : F) + 1)) = 1 ∧ (s₁ : F) * (s₃ : F) ≠ 1 := by
  set t : F := (u ^ 2)⁻¹ with ht
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have ht0 : t ≠ 0 := inv_ne_zero hu2
  have hex : ∃ a : F, a * (a - 1) * ((a - t) * (a ^ 2 - t * a + t)) ≠ 0 := by
    let f : F[X] := X * (X - 1) * ((X - C t) * (X ^ 2 - C t * X + C t))
    have hf : f ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) (mul_ne_zero ?_ ?_)
      · intro h; simpa using congrArg (fun p => p.coeff 0) h
      · intro h; simpa [ht0] using congrArg (fun p => p.coeff 0) h
      · intro h; simpa using congrArg (fun p => p.coeff 2) h
    have hdeg : f.natDegree < Nat.card F := by
      have : f.natDegree ≤ 5 := by simp only [f]; compute_degree
      omega
    obtain ⟨a, ha⟩ := exists_eval_ne_zero_fin f hf hdeg
    exact ⟨a, by simpa [f] using ha⟩
  obtain ⟨a, ha⟩ := hex
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have ha1 : a - 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hat : a - t ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul ha)
  have hq : a ^ 2 - t * a + t ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul ha)
  have hb : t / a - 1 ≠ 0 := by
    intro h0
    apply hat
    field_simp at h0
    linear_combination -h0
  refine ⟨Units.mk0 (a - 1) ha1, Units.mk0 (t / a - 1) hb, ?_, ?_⟩
  · simp only [Units.val_mk0]
    have : u ^ 2 * t = 1 := by rw [ht]; field_simp
    calc u ^ 2 * ((a - 1 + 1) * (t / a - 1 + 1)) = u ^ 2 * t := by
          field_simp
          ring
      _ = 1 := this
  · simp only [Units.val_mk0]
    intro h1
    apply hq
    field_simp at h1
    linear_combination -h1

theorem eq_top_of_uSL_ne_zero (h2 : (2 : F) ≠ 0) {H : Subgroup (SL2 F)}
    (hA : ∀ t : Fˣ, HSL t ∈ H) {c₀ : F} (hc₀ : c₀ ≠ 0) (hc₀H : uSL c₀ ∈ H) {g : SL2 F}
    (hg : g ∈ H) (hg10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : H = ⊤ := by
  have hsq : ∀ t : F, uSL (t ^ 2 * c₀) ∈ H := by
    intro t
    by_cases ht : t = 0
    · rw [ht, zero_pow two_ne_zero, zero_mul, uSL_zero_tt]
      exact H.one_mem
    · have := H.mul_mem (H.mul_mem (hA (Units.mk0 t ht)) hc₀H) (H.inv_mem (hA (Units.mk0 t ht)))
      rwa [HSL_conj_uSL_tt] at this
  have hU : ∀ c : F, uSL c ∈ H := by
    intro c
    have e : c = ((c / c₀ + 1) / 2) ^ 2 * c₀ - ((c / c₀ - 1) / 2) ^ 2 * c₀ := by
      field_simp
      ring
    rw [e, uSL_sub_tt]
    exact H.mul_mem (hsq _) (H.inv_mem (hsq _))
  have hW : (WSL : SL2 F) ∈ H := by
    obtain ⟨X, Y, hXH, hYH, hform⟩ : ∃ X Y : SL2 F, X ∈ H ∧ Y ∈ H ∧ g = X * WSL * Y :=
      ⟨_, _, H.mul_mem (hU _) (hA _), hU _, eq_uSL_mul_HSL_mul_WSL_mul_uSL hg10⟩
    have : (WSL : SL2 F) = X⁻¹ * g * Y⁻¹ := by
      rw [hform]
      group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hXH) hg) (H.inv_mem hYH)
  refine eq_top_iff.mpr fun g _ => ?_
  exact SL2_induction (p := fun g : SL2 F => g ∈ H) (fun g g' => H.mul_mem) hU hA hW g

theorem HSL_inv_mul_eq_uSL {P : SL2 F} (hP : (P : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ρ : Fˣ) (hρ : (ρ : F) = (P : Matrix (Fin 2) (Fin 2) F) 0 0) :
    HSL ρ⁻¹ * P = uSL ((P : Matrix (Fin 2) (Fin 2) F) 0 1 / (ρ : F)) := by
  have hdet := det_SL2 P
  rw [hP, mul_zero, sub_zero] at hdet
  have hρ0 : (ρ : F) ≠ 0 := ρ.ne_zero
  apply SL2_ext
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, Matrix.mul_apply,
      Fin.sum_univ_two, hP, ← hρ]
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, Matrix.mul_apply,
      Fin.sum_univ_two]
    field_simp
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, Matrix.mul_apply,
      Fin.sum_univ_two, hP]
  · simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, Matrix.mul_apply,
      Fin.sum_univ_two]
    rw [← hρ] at hdet
    linear_combination hdet

theorem eq_top_of_normTorus_seven [Finite F] (h7 : 7 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (κ : Fˣ)
    {H : Subgroup (SL2 F)} (hA : ∀ t : Fˣ, HSL t ∈ H)
    (hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ H) :
    H = ⊤ := by
  obtain ⟨u, v, h, hu, hv⟩ := exists_conic_point_seven h7 h2 (κ : F)
  obtain ⟨s₁, s₃, hrel, hs⟩ := exists_three_params h7 hu
  obtain ⟨hP10, hP01⟩ := normTorus_prod_three_entries (κ : F) u v h s₁ s₃ hrel
  set P : SL2 F := normTorusSL (κ : F) s₁ u v h * normTorusSL (κ : F) 1 u v h *
    normTorusSL (κ : F) s₃ u v h with hPdef
  have hPH : P ∈ H := H.mul_mem (H.mul_mem (hB s₁ u v h) (hB 1 u v h)) (hB s₃ u v h)
  have hdet := det_SL2 P
  have hP00 : (P : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := SL2_apply_zero_zero_ne_zero hP10
  set ρ : Fˣ := Units.mk0 _ hP00 with hρ
  have hc₀H : uSL ((P : Matrix (Fin 2) (Fin 2) F) 0 1 / (ρ : F)) ∈ H := by
    rw [← HSL_inv_mul_eq_uSL hP10 ρ rfl]
    exact H.mul_mem (hA _) hPH
  have hc₀ : (P : Matrix (Fin 2) (Fin 2) F) 0 1 / (ρ : F) ≠ 0 := by
    refine div_ne_zero ?_ ρ.ne_zero
    rw [hP01]
    exact mul_ne_zero hv (sub_ne_zero.mpr (Ne.symm hs))
  refine eq_top_of_uSL_ne_zero h2 hA hc₀ hc₀H (hB 1 u v h) ?_
  simp only [coe_normTorusSL, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
    inv_one, Units.val_one, one_mul]
  exact mul_ne_zero κ.ne_zero hv

end Seven

end CFSG.ClassicalInvolution.G2D4Models
