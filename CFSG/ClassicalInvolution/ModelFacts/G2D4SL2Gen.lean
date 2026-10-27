module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus7
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusGen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

section Gen

variable {F : Type} [Field F] [Finite F] {G : Type*} [Group G] {Φ : SL2 F →* G}

theorem chart_antidiag_of_inverts (h4 : 4 ≤ Nat.card F) (hΦ : Function.Injective Φ) {y : G}
    {D : GL (Fin 2) F} (hD : ∀ A : SL2 F, y * Φ A * y⁻¹ = Φ (glConjSL D A))
    (hinv : ∀ t : Fˣ, y * Φ (HSL t) * y⁻¹ = (Φ (HSL t))⁻¹) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one_fin h4
  have h1 := hinv t
  rw [hD, ← map_inv Φ] at h1
  have h2 := hΦ h1
  have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) h2
  simp only [glConjSL_coe] at h3
  have h4' : (D : Matrix (Fin 2) (Fin 2) F) * (HSL t : Matrix (Fin 2) (Fin 2) F) =
      (((HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    rw [← h3, Matrix.mul_assoc, Matrix.mul_assoc, gl_inv_mul D, Matrix.mul_one]
  have e00 := congrFun (congrFun h4' 0) 0
  have e11 := congrFun (congrFun h4' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_HSL, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two] at e00 e11
  have htne : (t : F) - (t : F)⁻¹ ≠ 0 := by
    intro h
    apply ht
    apply Units.ext
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    field_simp at h
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination h
  refine ⟨?_, ?_⟩
  · have : (D : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right htne
  · have : (D : Matrix (Fin 2) (Fin 2) F) 1 1 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right htne

theorem chart_le_sup_centralizer (h7 : 7 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (hΦ : Function.Injective Φ) {M : Subgroup G} {y : G} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * Φ A * y⁻¹ = Φ (glConjSL D A))
    (hinv : ∀ t : Fˣ, y * Φ (HSL t) * y⁻¹ = (Φ (HSL t))⁻¹) (hH : ∀ t : Fˣ, Φ (HSL t) ∈ M)
    (hdiag : ∀ s : Fˣ, ∃ g ∈ M, ∀ A : SL2 F, g * Φ A * g⁻¹ = Φ (glConjSL (diagGL s) A))
    (A : SL2 F) : Φ A ∈ M ⊔ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨hD00, hD11⟩ := chart_antidiag_of_inverts (by omega) hΦ hD hinv
  have hdet : (D : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (D : Matrix (Fin 2) (Fin 2) F)).mp D.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two, hD00, hD11] at hdet
  have hq : (D : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hr : (D : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  set q := (D : Matrix (Fin 2) (Fin 2) F) 0 1 with hqdef
  set r := (D : Matrix (Fin 2) (Fin 2) F) 1 0 with hrdef
  have hDeta : (D : Matrix (Fin 2) (Fin 2) F) = !![0, q; r, 0] := by
    rw [Matrix.eta_fin_two (D : Matrix (Fin 2) (Fin 2) F), hD00, hD11]
  set κ : Fˣ := Units.mk0 (q * r) (mul_ne_zero hq hr) with hκ
  set N := M ⊔ Subgroup.centralizer ({y} : Set G) with hN
  have hMN : M ≤ N := le_sup_left
  have hCN : Subgroup.centralizer ({y} : Set G) ≤ N := le_sup_right
  have hA : ∀ t : Fˣ, HSL t ∈ N.comap Φ := fun t => hMN (hH t)
  have hB : ∀ (s : Fˣ) (u v : F) (h : u ^ 2 - (κ : F) * v ^ 2 = 1),
      normTorusSL (κ : F) s u v h ∈ N.comap Φ := by
    intro s u v h
    rw [Subgroup.mem_comap]
    have hu₀ : u * u - (q * v) * (r * v) = 1 := by
      have hk : (κ : F) = q * r := rfl
      rw [hk] at h
      linear_combination h
    let B₀ : SL2 F := ⟨!![u, q * v; r * v, u], by
      rw [det_fin_two]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      linear_combination hu₀⟩
    set s' : Fˣ := s * (Units.mk0 q hq)⁻¹ with hs'
    have hconj : normTorusSL (κ : F) s u v h = glConjSL (diagGL s') B₀ := by
      have hq0 : q ≠ 0 := hq
      have hs0 : (s : F) ≠ 0 := s.ne_zero
      have hκv : (κ : F) = q * r := rfl
      refine SL2_ext ?_ ?_ ?_ ?_
      · rw [glConjSL_diagGL_apply_00]
        simp [coe_normTorusSL, B₀]
      · rw [glConjSL_diagGL_apply_01]
        simp [coe_normTorusSL, B₀, hs']
        field_simp
      · rw [glConjSL_diagGL_apply_10]
        simp [coe_normTorusSL, B₀, hs', hκv]
        field_simp
      · rw [glConjSL_diagGL_apply_11]
        simp [coe_normTorusSL, B₀]
    have hcomm : (D : Matrix (Fin 2) (Fin 2) F) * (B₀ : Matrix (Fin 2) (Fin 2) F) =
        (B₀ : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
      rw [hDeta]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hglB : glConjSL D B₀ = B₀ :=
      Subtype.ext (by rw [glConjSL_coe, hcomm, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one])
    have hyB : y * Φ B₀ = Φ B₀ * y := by
      have := hD B₀
      rw [hglB] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have hP : Φ B₀ ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyB.symm
    obtain ⟨g, hgM, hg⟩ := hdiag s'
    rw [hconj, ← hg B₀]
    exact mul_mem (mul_mem (hMN hgM) (hCN hP)) (inv_mem (hMN hgM))
  have htop := eq_top_of_normTorus_seven h7 h2 κ hA hB
  have : A ∈ N.comap Φ := by rw [htop]; trivial
  exact this

end Gen

end CFSG.ClassicalInvolution.G2D4Models
