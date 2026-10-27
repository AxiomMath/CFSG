module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Closure

variable {F : Type} [Field F]

theorem innerLift_mul {φ ψ : MulAut SL(4, F)} {x y : GL (Fin 4) F} (hφ : InnerLift φ x) (hψ : InnerLift ψ y) :
    InnerLift (φ * ψ) (x * y) := by
  intro g
  rw [MulAut.mul_apply, hφ (ψ g), hψ g, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem innerLift_inv {φ : MulAut SL(4, F)} {x : GL (Fin 4) F} (hφ : InnerLift φ x) : InnerLift φ⁻¹ x⁻¹ := by
  intro g
  have h := hφ (φ⁻¹ g)
  rw [MulAut.apply_inv_self] at h
  rw [inv_inv]
  have hx1 : ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul x
  have hx2 : (x : Matrix (Fin 4) (Fin 4) F) * ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv x
  calc ((φ⁻¹ g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
      = ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x * ((φ⁻¹ g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) := by
        simp only [← Matrix.mul_assoc, hx1, Matrix.one_mul]
        simp only [Matrix.mul_assoc, hx1, Matrix.mul_one]
    _ = _ := by rw [← h]

theorem isInnerDiag4_mul {φ ψ : MulAut SL(4, F)} (hφ : IsInnerDiag4 φ) (hψ : IsInnerDiag4 ψ) :
    IsInnerDiag4 (φ * ψ) := by
  obtain ⟨x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := hψ
  exact ⟨x * y, innerLift_mul hx hy⟩

theorem isInnerDiag4_inv {φ : MulAut SL(4, F)} (hφ : IsInnerDiag4 φ) : IsInnerDiag4 φ⁻¹ := by
  obtain ⟨x, hx⟩ := hφ
  exact ⟨x⁻¹, innerLift_inv hx⟩

theorem coe_glT_inv (C : GL (Fin 4) F) : ((glT C)⁻¹ : GL (Fin 4) F) = glT C⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_glT, coe_glT, ← Matrix.transpose_mul, coe_inv_mul C, Matrix.transpose_one]
  rfl

theorem innerLift_graph_mul {u v : MulAut SL(4, F)} {B C : GL (Fin 4) F} (hu : GraphForm u B)
    (hv : GraphForm v C) : InnerLift (u * v) (B * (glT C)⁻¹) := by
  intro x
  have hinv : ((v x)⁻¹ : SL(4, F)) = v x⁻¹ := (map_inv v x).symm
  rw [MulAut.mul_apply, hu (v x), hinv, hv x⁻¹, _root_.mul_inv_rev, inv_inv (glT C), coe_glT_inv]
  simp only [Units.val_mul, coe_glT, Matrix.transpose_mul, Matrix.transpose_transpose, inv_inv, Matrix.mul_assoc]

end Closure

section Fix

variable {F : Type} [Field F]

theorem innerLift_fix {t : MulAut SL(4, F)} {g : GL (Fin 4) F} (ht : InnerLift t g) (x : SL(4, F))
    (hx : (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F)) : t x = x := by
  apply Subtype.ext
  rw [ht x, ← hx, Matrix.mul_assoc, coe_mul_inv g, Matrix.mul_one]

theorem graphEq_fix {u : MulAut SL(4, F)} {M Mi : Matrix (Fin 4) (Fin 4) F} (hMi : M * Mi = 1)
    (hu : GraphEq u M) (x : SL(4, F))
    (hx : (x : Matrix (Fin 4) (Fin 4) F) * M * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = M) : u x = x := by
  apply Subtype.ext
  have hxx : (x : Matrix (Fin 4) (Fin 4) F)ᵀ * ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have : ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.transpose_one]
  have h2 : (x : Matrix (Fin 4) (Fin 4) F) * M = M * ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    calc (x : Matrix (Fin 4) (Fin 4) F) * M
        = (x : Matrix (Fin 4) (Fin 4) F) * M * ((x : Matrix (Fin 4) (Fin 4) F)ᵀ *
            ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ) := by rw [hxx, Matrix.mul_one]
      _ = ((x : Matrix (Fin 4) (Fin 4) F) * M * (x : Matrix (Fin 4) (Fin 4) F)ᵀ) *
            ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hx]
  calc ((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
      = ((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (M * Mi) := by rw [hMi, Matrix.mul_one]
    _ = (((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * M) * Mi := by rw [Matrix.mul_assoc]
    _ = ((x : Matrix (Fin 4) (Fin 4) F) * M) * Mi := by rw [hu x, h2]
    _ = x := by rw [Matrix.mul_assoc, hMi, Matrix.mul_one]

theorem eq_one_of_innerLift_scalar {t : MulAut SL(4, F)} {g : GL (Fin 4) F} (ht : InnerLift t g) (c : F)
    (hc : (g : Matrix (Fin 4) (Fin 4) F) = c • (1 : Matrix (Fin 4) (Fin 4) F)) : t = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hg : c • ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have := coe_mul_inv g
    rw [hc, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  rw [ht x, hc, MulAut.one_apply]
  calc (c • (1 : Matrix (Fin 4) (Fin 4) F)) * (x : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = (x : Matrix (Fin 4) (Fin 4) F) * (c • ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = x := by rw [hg, Matrix.mul_one]

end Fix

section Pfaff

variable {F : Type} [Field F]

theorem isSquare_det_of_skew (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 4) (Fin 4) F) (hM : Mᵀ = -M) : IsSquare M.det := by
  have hs : ∀ i j, M j i = - M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  have hd : ∀ i, M i i = 0 := fun i => by
    have := hs i i
    have h3 : (2 : F) * M i i = 0 := by linear_combination this
    exact (mul_eq_zero.1 h3).resolve_left h2
  refine ⟨M 0 1 * M 2 3 - M 0 2 * M 1 3 + M 0 3 * M 1 2, ?_⟩
  have e10 := hs 0 1
  have e20 := hs 0 2
  have e30 := hs 0 3
  have e21 := hs 1 2
  have e31 := hs 1 3
  have e32 := hs 2 3
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, hd, e10, e20, e30, e21, e31, e32]
  ring

end Pfaff

section TypeData

variable {F : Type} [Field F]

theorem isSquare_mul_of_not_isSquare [Finite F] {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by simp [h]⟩
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have h3 : quadraticChar F (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 h3

theorem not_isSquare_neg_one [Finite F] (hF4 : Nat.card F % 4 = 3) : ¬ IsSquare (-1 : F) := by
  classical
  have := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
  omega

theorem det_sq_of_sq (g : Matrix (Fin 4) (Fin 4) F) (μ : F) (h : g * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)) :
    g.det = μ ^ 2 ∨ g.det = -μ ^ 2 := by
  have h1 : g.det * g.det = (μ ^ 2) ^ 2 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at this
    simp only [Fintype.card_fin, mul_one] at this
    linear_combination this
  have h2 : (g.det - μ ^ 2) * (g.det + μ ^ 2) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · left; linear_combination h3
  · right; linear_combination h3

theorem det_eq_of_isSquare [Finite F] (hF4 : Nat.card F % 4 = 3) {g : Matrix (Fin 4) (Fin 4) F} {μ : F}
    (h : g * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)) (hμ : μ ≠ 0) (hsq : IsSquare g.det) : g.det = μ ^ 2 := by
  rcases det_sq_of_sq g μ h with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hsq
    obtain ⟨c, hc⟩ := hsq
    apply not_isSquare_neg_one hF4
    refine ⟨c / μ, ?_⟩
    field_simp
    linear_combination hc

theorem split_norm [Finite F] (hF4 : Nat.card F % 4 = 3) {g : Matrix (Fin 4) (Fin 4) F} {μ : F} (hμ : μ ≠ 0)
    (hgg : g * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)) (hdet : IsSquare g.det) (hsq : IsSquare μ) :
    ∃ ν : F, ν ≠ 0 ∧ (ν⁻¹ • g) * (ν⁻¹ • g) = (1 : Matrix (Fin 4) (Fin 4) F) ∧ (ν⁻¹ • g).det = 1 := by
  obtain ⟨ν, hν⟩ := hsq
  have hν0 : ν ≠ 0 := fun h => hμ (by rw [hν, h, mul_zero])
  have hd := det_eq_of_isSquare hF4 hgg hμ hdet
  refine ⟨ν, hν0, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgg, smul_smul, hν]
    have : ν⁻¹ * ν⁻¹ * (ν * ν) = 1 := by field_simp
    rw [this, one_smul]
  · rw [Matrix.det_smul, hd, hν]
    simp only [Fintype.card_fin]
    field_simp

theorem ext_norm [Finite F] (hF4 : Nat.card F % 4 = 3) {g : Matrix (Fin 4) (Fin 4) F} {μ : F} (hμ : μ ≠ 0)
    (hgg : g * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)) (hns : ¬ IsSquare μ) :
    ∃ l : F, l ≠ 0 ∧ (l • g) * (l • g) = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have hμi : ¬ IsSquare μ⁻¹ := fun h => hns (by simpa using h.inv)
  obtain ⟨l, hl⟩ := isSquare_mul_of_not_isSquare (not_isSquare_neg_one hF4) hμi
  have hl0 : l ≠ 0 := by
    intro h
    have h0 : (-1 : F) * μ⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.2 one_ne_zero) (inv_ne_zero hμ)
    exact h0 (by rw [hl, h, mul_zero])
  refine ⟨l, hl0, ?_⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgg, smul_smul]
  have : l * l * μ = -1 := by
    rw [← hl]; field_simp
  rw [this]

theorem type_data [Finite F] {u t : MulAut SL(4, F)} {B g : GL (Fin 4) F}
    (hu : GraphForm u B) (hBt : (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B)
    (hBd : ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) F).det)
    (ht : InnerLift t g) (ht2 : t * t = 1) {B' : GL (Fin 4) F} (hB' : GraphForm (t * u) B')
    (hB't : (B' : Matrix (Fin 4) (Fin 4) F)ᵀ = B') (hB'd : ¬ IsSquare (B' : Matrix (Fin 4) (Fin 4) F).det) :
    (∃ μ : F, μ ≠ 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) * g = μ • (1 : Matrix (Fin 4) (Fin 4) F)) ∧
      (g : Matrix (Fin 4) (Fin 4) F) * B = B * (g : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      IsSquare (g : Matrix (Fin 4) (Fin 4) F).det := by
  obtain ⟨ν, hν⟩ := graphEq_unique (coe_inv_mul B') (coe_mul_inv B') hB'.graphEq (graphEq_inner_mul hu ht)
  refine ⟨innerLift_sq ht ht2, ?_, ?_⟩
  · have h1 := congrArg Matrix.transpose hν
    rw [Matrix.transpose_mul, Matrix.transpose_smul, hB't, hBt] at h1
    exact hν.trans h1.symm
  · have hdB : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
    have hd := congrArg Matrix.det hν
    rw [Matrix.det_mul, Matrix.det_smul] at hd
    simp only [Fintype.card_fin] at hd
    have hsq : IsSquare ((B' : Matrix (Fin 4) (Fin 4) F).det * ((B : Matrix (Fin 4) (Fin 4) F).det)⁻¹) :=
      isSquare_mul_of_not_isSquare hB'd (fun h => hBd (by simpa using h.inv))
    have : (g : Matrix (Fin 4) (Fin 4) F).det = (ν ^ 2 * ν ^ 2) * ((B' : Matrix (Fin 4) (Fin 4) F).det *
        ((B : Matrix (Fin 4) (Fin 4) F).det)⁻¹) := by
      field_simp
      linear_combination hd
    rw [this]
    exact IsSquare.mul ⟨ν ^ 2, rfl⟩ hsq

end TypeData

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
