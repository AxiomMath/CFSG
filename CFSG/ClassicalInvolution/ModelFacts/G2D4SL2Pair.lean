module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Pair

variable {G : Type*} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {Φ₁ : SL2 F₁ →* G} {Φ₂ : SL2 F₂ →* G}
  (hcomm : ∀ (A : SL2 F₁) (B : SL2 F₂), Φ₁ A * Φ₂ B = Φ₂ B * Φ₁ A)

include hcomm in
theorem pair_conj_chart1_aux (R : SL2 F₁) (S : SL2 F₂) (C : SL2 F₁) :
    (Φ₁ R * Φ₂ S) * Φ₁ C * (Φ₁ R * Φ₂ S)⁻¹ = Φ₁ (R * C * R⁻¹) := by
  have h1 : Φ₂ S * Φ₁ C * (Φ₂ S)⁻¹ = Φ₁ C := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hcomm C S).symm
  calc (Φ₁ R * Φ₂ S) * Φ₁ C * (Φ₁ R * Φ₂ S)⁻¹
      = Φ₁ R * (Φ₂ S * Φ₁ C * (Φ₂ S)⁻¹) * (Φ₁ R)⁻¹ := by group
    _ = _ := by rw [h1, ← map_inv, ← map_mul, ← map_mul]

include hcomm in
theorem pair_conj_chart2_aux (R : SL2 F₁) (S : SL2 F₂) (C : SL2 F₂) :
    (Φ₁ R * Φ₂ S) * Φ₂ C * (Φ₁ R * Φ₂ S)⁻¹ = Φ₂ (S * C * S⁻¹) := by
  calc (Φ₁ R * Φ₂ S) * Φ₂ C * (Φ₁ R * Φ₂ S)⁻¹
      = Φ₁ R * (Φ₂ S * Φ₂ C * (Φ₂ S)⁻¹) * (Φ₁ R)⁻¹ := by group
    _ = Φ₁ R * Φ₂ (S * C * S⁻¹) * (Φ₁ R)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = Φ₂ (S * C * S⁻¹) := by
        rw [mul_inv_eq_iff_eq_mul]; exact hcomm R _

include hcomm in
theorem pair_inv_eq (R : SL2 F₁) (S : SL2 F₂) :
    (Φ₁ R * Φ₂ S)⁻¹ = Φ₁ R⁻¹ * Φ₂ S⁻¹ := by
  rw [_root_.mul_inv_rev, ← map_inv Φ₁, ← map_inv Φ₂]
  exact (hcomm R⁻¹ S⁻¹).symm

include hcomm in
theorem pair_conj_chart1 {z : G} {g : GL (Fin 2) F₁}
    (hz : ∀ C : SL2 F₁, z * Φ₁ C * z⁻¹ = Φ₁ (glConjSL g C)) (R : SL2 F₁) (S : SL2 F₂)
    (C : SL2 F₁) :
    ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹) * Φ₁ C * ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹)⁻¹ =
      Φ₁ (glConjSL (Matrix.SpecialLinearGroup.toGL R * g *
        (Matrix.SpecialLinearGroup.toGL R)⁻¹) C) := by
  have hxc := pair_conj_chart1_aux hcomm
  have hinv := pair_inv_eq hcomm R S
  have hxc' : (Φ₁ R * Φ₂ S)⁻¹ * Φ₁ C * (Φ₁ R * Φ₂ S) = Φ₁ (R⁻¹ * C * R) := by
    have := hxc R⁻¹ S⁻¹ C
    rw [← pair_inv_eq hcomm R S, inv_inv] at this
    simpa [inv_inv] using this
  calc (Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹ * Φ₁ C * ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹)⁻¹
      = (Φ₁ R * Φ₂ S) * (z * ((Φ₁ R * Φ₂ S)⁻¹ * Φ₁ C * (Φ₁ R * Φ₂ S)) * z⁻¹) *
          (Φ₁ R * Φ₂ S)⁻¹ := by group
    _ = _ := by
      rw [hxc', hz, hxc R S, glConjSL_mul, glConjSL_mul, ← map_inv, glConjSL_toGL,
        glConjSL_toGL, inv_inv]

include hcomm in
theorem pair_conj_chart2 {z : G} {g : GL (Fin 2) F₂}
    (hz : ∀ C : SL2 F₂, z * Φ₂ C * z⁻¹ = Φ₂ (glConjSL g C)) (R : SL2 F₁) (S : SL2 F₂)
    (C : SL2 F₂) :
    ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹) * Φ₂ C * ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹)⁻¹ =
      Φ₂ (glConjSL (Matrix.SpecialLinearGroup.toGL S * g *
        (Matrix.SpecialLinearGroup.toGL S)⁻¹) C) := by
  have hxc := pair_conj_chart2_aux hcomm
  have hxc' : (Φ₁ R * Φ₂ S)⁻¹ * Φ₂ C * (Φ₁ R * Φ₂ S) = Φ₂ (S⁻¹ * C * S) := by
    have := hxc R⁻¹ S⁻¹ C
    rw [← pair_inv_eq hcomm R S, inv_inv] at this
    simpa [inv_inv] using this
  calc (Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹ * Φ₂ C * ((Φ₁ R * Φ₂ S) * z * (Φ₁ R * Φ₂ S)⁻¹)⁻¹
      = (Φ₁ R * Φ₂ S) * (z * ((Φ₁ R * Φ₂ S)⁻¹ * Φ₂ C * (Φ₁ R * Φ₂ S)) * z⁻¹) *
          (Φ₁ R * Φ₂ S)⁻¹ := by group
    _ = _ := by
      rw [hxc', hz, hxc R S, glConjSL_mul, glConjSL_mul, ← map_inv, glConjSL_toGL,
        glConjSL_toGL, inv_inv]

include hcomm in
theorem pair_prod_conj1 {t : G} {s : F₁ˣ}
    (hs : ∀ C : SL2 F₁, t * Φ₁ C * t⁻¹ = Φ₁ (glConjSL (diagGL s) C)) (A : SL2 F₁) (B : SL2 F₂)
    (C : SL2 F₁) :
    (t * Φ₁ A * Φ₂ B) * Φ₁ C * (t * Φ₁ A * Φ₂ B)⁻¹ =
      Φ₁ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL A) C) := by
  have h1 : Φ₂ B * Φ₁ C * (Φ₂ B)⁻¹ = Φ₁ C := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hcomm C B).symm
  have h2 := hs (A * C * A⁻¹)
  rw [glConjSL_mul, glConjSL_toGL, ← h2, map_mul, map_mul, map_inv]
  calc t * Φ₁ A * Φ₂ B * Φ₁ C * (t * Φ₁ A * Φ₂ B)⁻¹
      = t * (Φ₁ A * (Φ₂ B * Φ₁ C * (Φ₂ B)⁻¹) * (Φ₁ A)⁻¹) * t⁻¹ := by group
    _ = _ := by rw [h1]

include hcomm in
theorem pair_prod_conj2 {t : G} {s : F₂ˣ}
    (hs : ∀ C : SL2 F₂, t * Φ₂ C * t⁻¹ = Φ₂ (glConjSL (diagGL s) C)) (A : SL2 F₁) (B : SL2 F₂)
    (C : SL2 F₂) :
    (t * Φ₁ A * Φ₂ B) * Φ₂ C * (t * Φ₁ A * Φ₂ B)⁻¹ =
      Φ₂ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL B) C) := by
  have h1 : Φ₁ A * Φ₂ (B * C * B⁻¹) * (Φ₁ A)⁻¹ = Φ₂ (B * C * B⁻¹) := by
    rw [mul_inv_eq_iff_eq_mul]; exact hcomm A _
  have h2 := hs (B * C * B⁻¹)
  rw [glConjSL_mul, glConjSL_toGL, ← h2]
  calc t * Φ₁ A * Φ₂ B * Φ₂ C * (t * Φ₁ A * Φ₂ B)⁻¹
      = t * (Φ₁ A * (Φ₂ B * Φ₂ C * (Φ₂ B)⁻¹) * (Φ₁ A)⁻¹) * t⁻¹ := by group
    _ = t * Φ₂ (B * C * B⁻¹) * t⁻¹ := by
        have h1' : Φ₁ A * (Φ₂ B * Φ₂ C * (Φ₂ B)⁻¹) * (Φ₁ A)⁻¹ = Φ₂ B * Φ₂ C * (Φ₂ B)⁻¹ := by
          have := h1
          simp only [map_mul, map_inv] at this
          exact this
        rw [h1']
        simp [map_mul, map_inv]

end Pair

section Scalar

variable {F : Type} [Field F]

theorem glConjSL_of_scalar {g : GL (Fin 2) F} {c : F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = c • 1) (C : SL2 F) : glConjSL g C = C := by
  apply Subtype.ext
  rw [glConjSL_coe]
  have h1 : (g : Matrix (Fin 2) (Fin 2) F) * (C : Matrix (Fin 2) (Fin 2) F) =
      (C : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [hg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]

theorem diag_mul_scalar (s : Fˣ) (A : SL2 F) (c : F)
    (h : ((diagGL s * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = c • 1) : ∃ u : Fˣ, A = HSL u ∧ s = u⁻¹ * u⁻¹ := by
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  have hs0 : (s : F) ≠ 0 := s.ne_zero
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 A
  have hdet' : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [e01] at hdet; simpa using hdet
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  set u : Fˣ := Units.mk0 _ hA00 with hu
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((u⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right hdet'
  refine ⟨u, ?_, ?_⟩
  · apply SL2_ext
    · simp [coe_HSL, hu]
    · simp [coe_HSL, e01]
    · simp [coe_HSL, e10]
    · rw [hA11]; simp [coe_HSL]
  · have h1 : s * u = u⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, ← hA11, hu, Units.val_mk0, e00, e11]
    exact eq_mul_inv_of_mul_eq h1

end Scalar

section Main

variable {G : Type*} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {Φ₁ : SL2 F₁ →* G} {Φ₂ : SL2 F₂ →* G}

theorem exists_conj_to_torus_mul_abs (h2₁ : (2 : F₁) ≠ 0) (h2₂ : (2 : F₂) ≠ 0)
    (hΦ₁ : Function.Injective Φ₁) (hΦ₂ : Function.Injective Φ₂)
    (hcomm : ∀ (A : SL2 F₁) (B : SL2 F₂), Φ₁ A * Φ₂ B = Φ₂ B * Φ₁ A) {T SP : Subgroup G}
    (hT₁ : ∀ t ∈ T, ∃ s : F₁ˣ, ∀ C : SL2 F₁, t * Φ₁ C * t⁻¹ = Φ₁ (glConjSL (diagGL s) C))
    (hT₂ : ∀ t ∈ T, ∃ s : F₂ˣ, ∀ C : SL2 F₂, t * Φ₂ C * t⁻¹ = Φ₂ (glConjSL (diagGL s) C))
    (hH₁ : ∀ u : F₁ˣ, Φ₁ (HSL u) ∈ T) (hH₂ : ∀ u : F₂ˣ, Φ₂ (HSL u) ∈ T)
    (hSP : ∀ g ∈ SP, ∃ t ∈ T, ∃ (A : SL2 F₁) (B : SL2 F₂), g = t * Φ₁ A * Φ₂ B)
    (hSPmem : ∀ (R : SL2 F₁) (S : SL2 F₂), Φ₁ R * Φ₂ S ∈ SP) {τ : G}
    (hscal₁ : ∀ z ∈ SP, z * z = 1 → (∀ C : SL2 F₁, z * Φ₁ C = Φ₁ C * z) → z = 1 ∨ z = τ)
    (hscal₂ : ∀ z ∈ SP, z * z = 1 → (∀ C : SL2 F₂, z * Φ₂ C = Φ₂ C * z) → z = 1 ∨ z = τ)
    {z : G} (hz : z ∈ SP) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzτ : z ≠ τ) :
    ∃ x ∈ SP, ∃ t ∈ T, x * z * x⁻¹ = t * (Φ₁ WSL * Φ₂ WSL) := by
  obtain ⟨t, ht, A, B, hzdef⟩ := hSP z hz
  obtain ⟨s₁, hs₁⟩ := hT₁ t ht
  obtain ⟨s₂, hs₂⟩ := hT₂ t ht
  set gA : GL (Fin 2) F₁ := diagGL s₁ * Matrix.SpecialLinearGroup.toGL A with hgA
  set gB : GL (Fin 2) F₂ := diagGL s₂ * Matrix.SpecialLinearGroup.toGL B with hgB
  have hzA : ∀ C : SL2 F₁, z * Φ₁ C * z⁻¹ = Φ₁ (glConjSL gA C) := by
    intro C
    rw [hzdef]
    exact pair_prod_conj1 hcomm hs₁ A B C
  have hzB : ∀ C : SL2 F₂, z * Φ₂ C * z⁻¹ = Φ₂ (glConjSL gB C) := by
    intro C
    rw [hzdef]
    exact pair_prod_conj2 hcomm hs₂ A B C
  obtain ⟨lA, hlA0, hlA⟩ := sq_scalar_of_chart hΦ₁ hz2 hzA
  obtain ⟨lB, hlB0, hlB⟩ := sq_scalar_of_chart hΦ₂ hz2 hzB
  by_cases hsA : ∃ c : F₁, (gA : Matrix (Fin 2) (Fin 2) F₁) = c • 1
  · exfalso
    obtain ⟨c, hc⟩ := hsA
    rcases hscal₁ z hz hz2 (fun C => by
      have := hzA C
      rw [glConjSL_of_scalar hc, mul_inv_eq_iff_eq_mul] at this
      exact this) with h | h
    · exact hz1 h
    · exact hzτ h
  by_cases hsB : ∃ c : F₂, (gB : Matrix (Fin 2) (Fin 2) F₂) = c • 1
  · exfalso
    obtain ⟨c, hc⟩ := hsB
    rcases hscal₂ z hz hz2 (fun C => by
      have := hzB C
      rw [glConjSL_of_scalar hc, mul_inv_eq_iff_eq_mul] at this
      exact this) with h | h
    · exact hz1 h
    · exact hzτ h
  obtain ⟨RA, bA, cA, hbA, hcA, hRA⟩ := exists_antidiag_conj h2₁
    (gA : Matrix (Fin 2) (Fin 2) F₁) hlA hlA0 (fun c hc => hsA ⟨c, hc⟩)
  obtain ⟨RB, bB, cB, hbB, hcB, hRB⟩ := exists_antidiag_conj h2₂
    (gB : Matrix (Fin 2) (Fin 2) F₂) hlB hlB0 (fun c hc => hsB ⟨c, hc⟩)
  set x : G := Φ₁ RA * Φ₂ RB with hx
  have hxSP : x ∈ SP := hSPmem RA RB
  refine ⟨x, hxSP, ?_⟩
  obtain ⟨t', ht', A', B', hz'⟩ := hSP (x * z * x⁻¹) (mul_mem (mul_mem hxSP hz) (inv_mem hxSP))
  obtain ⟨s₁', hs₁'⟩ := hT₁ t' ht'
  obtain ⟨s₂', hs₂'⟩ := hT₂ t' ht'
  have hDA : ((Matrix.SpecialLinearGroup.toGL RA * gA * (Matrix.SpecialLinearGroup.toGL RA)⁻¹ :
      GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) = !![0, bA; cA, 0] := by
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hRA
  have hDB : ((Matrix.SpecialLinearGroup.toGL RB * gB * (Matrix.SpecialLinearGroup.toGL RB)⁻¹ :
      GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) = !![0, bB; cB, 0] := by
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hRB
  have hA1 := pair_conj_chart1 hcomm hzA RA RB
  have hA2 : ∀ C : SL2 F₁, (x * z * x⁻¹) * Φ₁ C * (x * z * x⁻¹)⁻¹ =
      Φ₁ (glConjSL (diagGL s₁' * Matrix.SpecialLinearGroup.toGL A') C) := by
    intro C
    rw [hz']
    exact pair_prod_conj1 hcomm hs₁' A' B' C
  have hB1 := pair_conj_chart2 hcomm hzB RA RB
  have hB2 : ∀ C : SL2 F₂, (x * z * x⁻¹) * Φ₂ C * (x * z * x⁻¹)⁻¹ =
      Φ₂ (glConjSL (diagGL s₂' * Matrix.SpecialLinearGroup.toGL B') C) := by
    intro C
    rw [hz']
    exact pair_prod_conj2 hcomm hs₂' A' B' C
  obtain ⟨cA', -, hcA'⟩ := exists_scalar_of_glConjSL_eq
    (D := Matrix.SpecialLinearGroup.toGL RA * gA * (Matrix.SpecialLinearGroup.toGL RA)⁻¹)
    (E := diagGL s₁' * Matrix.SpecialLinearGroup.toGL A')
    (fun C => hΦ₁ ((hA1 C).symm.trans (hA2 C)))
  obtain ⟨cB', -, hcB'⟩ := exists_scalar_of_glConjSL_eq
    (D := Matrix.SpecialLinearGroup.toGL RB * gB * (Matrix.SpecialLinearGroup.toGL RB)⁻¹)
    (E := diagGL s₂' * Matrix.SpecialLinearGroup.toGL B')
    (fun C => hΦ₂ ((hB1 C).symm.trans (hB2 C)))
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hDA] at hcA'
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hDB] at hcB'
  obtain ⟨u, hu⟩ := exists_HSL_mul_WSL s₁' A' (cA' * bA) (cA' * cA) (by
    rw [hcA']; ext i j; fin_cases i <;> fin_cases j <;> simp)
  obtain ⟨v, hv⟩ := exists_HSL_mul_WSL s₂' B' (cB' * bB) (cB' * cB) (by
    rw [hcB']; ext i j; fin_cases i <;> fin_cases j <;> simp)
  refine ⟨t' * Φ₁ (HSL u) * Φ₂ (HSL v), mul_mem (mul_mem ht' (hH₁ u)) (hH₂ v), ?_⟩
  have hcomm' := hcomm WSL (HSL v)
  rw [hz', hu, hv, map_mul, map_mul]
  calc t' * (Φ₁ (HSL u) * Φ₁ WSL) * (Φ₂ (HSL v) * Φ₂ WSL)
      = t' * Φ₁ (HSL u) * (Φ₁ WSL * Φ₂ (HSL v)) * Φ₂ WSL := by group
    _ = t' * Φ₁ (HSL u) * (Φ₂ (HSL v) * Φ₁ WSL) * Φ₂ WSL := by rw [hcomm']
    _ = _ := by group

end Main

end CFSG.ClassicalInvolution.G2D4Models
