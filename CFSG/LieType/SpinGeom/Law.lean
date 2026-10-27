module

public import CFSG.LieType.SpinGeom.Frame

public section

namespace CFSG.LieType.SpinGeom

open scoped Matrix

section Algebra

variable {K : Type} [Field K]

@[expose] def crossS (a b : Fin 3 → K) : Fin 3 → K :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

theorem crossS_mulVec (g : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3 → K) :
    crossS (g *ᵥ a) (g *ᵥ b) = (g.adjugate)ᵀ *ᵥ crossS a b := by
  ext i
  fin_cases i <;>
    simp [crossS, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.adjugate_fin_three] <;>
    ring

theorem altMat_mulVec_eq_crossS [CharP K 2] (a b : Fin 3 → K) :
    altMat K a *ᵥ b = crossS a b := by
  ext i
  fin_cases i <;>
    simp [altMat, crossS, Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.sub_eq_add] <;>
    ring

theorem altMat_add (a b : Fin 3 → K) : altMat K (a + b) = altMat K a + altMat K b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem altMat_smul (r : K) (a : Fin 3 → K) : altMat K (r • a) = r • altMat K a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem altMat_zero : altMat K (0 : Fin 3 → K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem altMat_mulVec_comm (a b : Fin 3 → K) : altMat K a *ᵥ b = altMat K b *ᵥ a := by
  ext i
  fin_cases i <;> simp [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem dot_altMat_mulVec_comm (a b c : Fin 3 → K) :
    a ⬝ᵥ (altMat K b *ᵥ c) = c ⬝ᵥ (altMat K a *ᵥ b) := by
  simp [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem dot_altMat_self [CharP K 2] (a b : Fin 3 → K) : a ⬝ᵥ (altMat K a *ᵥ b) = 0 := by
  simp [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (a 0 * a 2 * b 1 + a 0 * a 1 * b 2 + a 1 * a 2 * b 0) * h

theorem dot_contra_mulVec (g : Matrix (Fin 3) (Fin 3) K) (hg : g.det = 1) (a b : Fin 3 → K) :
    ((g.adjugate)ᵀ *ᵥ a) ⬝ᵥ (g *ᵥ b) = a ⬝ᵥ b := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.adjugate_mul, hg, one_smul, Matrix.vecMul_one]

theorem contra_mul (g₁ g₂ : Matrix (Fin 3) (Fin 3) K) :
    ((g₁ * g₂).adjugate)ᵀ = (g₁.adjugate)ᵀ * (g₂.adjugate)ᵀ := by
  rw [Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

theorem altMat_mulVec_mulVec [CharP K 2] (g : Matrix (Fin 3) (Fin 3) K) (m x : Fin 3 → K) :
    altMat K (g *ᵥ m) *ᵥ (g *ᵥ x) = (g.adjugate)ᵀ *ᵥ (altMat K m *ᵥ x) := by
  rw [altMat_mulVec_eq_crossS, altMat_mulVec_eq_crossS, crossS_mulVec]

end Algebra

section Law

variable {K : Type} [Field K]

@[expose] noncomputable def xvec (K : Type) [Field K] (v : Fin (2 * 4) → K) : Fin 3 → K :=
  fun j => coordX K v j.succ

@[expose] noncomputable def yvec (K : Type) [Field K] (v : Fin (2 * 4) → K) : Fin 3 → K :=
  fun j => coordY K v j.succ

theorem coordX_spinElt_zero (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) :
    coordX K (spinElt K c m g v) 0 = coordX K v 0 + c ⬝ᵥ (g *ᵥ xvec K v) +
      m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ yvec K v) + coordY K v 0 * (c ⬝ᵥ m) := by
  unfold spinElt
  rw [coordX_frameVec_zero]
  rfl

theorem xvec_spinElt (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K) (v : Fin (2 * 4) → K) :
    xvec K (spinElt K c m g v) = g *ᵥ xvec K v + coordY K v 0 • m := by
  ext j
  unfold xvec spinElt
  rw [coordX_frameVec_succ]

theorem yvec_spinElt (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K) (v : Fin (2 * 4) → K) :
    yvec K (spinElt K c m g v) = (g.adjugate)ᵀ *ᵥ yvec K v + altMat K m *ᵥ (g *ᵥ xvec K v) +
      coordY K v 0 • c := by
  ext j
  unfold yvec spinElt
  rw [coordY_frameVec_succ]
  rfl

theorem coordY_spinElt_zero (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) : coordY K (spinElt K c m g v) 0 = coordY K v 0 := by
  unfold spinElt
  rw [coordY_frameVec_zero]

end Law

section Comp

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem spinElt_comp_xvec (c₁ m₁ : Fin 3 → K) (g₁ : Matrix (Fin 3) (Fin 3) K)
    (c₂ m₂ : Fin 3 → K) (g₂ : Matrix (Fin 3) (Fin 3) K) (v : Fin (2 * 4) → K) :
    xvec K (spinElt K c₁ m₁ g₁ (spinElt K c₂ m₂ g₂ v)) =
      (g₁ * g₂) *ᵥ xvec K v + coordY K v 0 • (m₁ + g₁ *ᵥ m₂) := by
  rw [xvec_spinElt, xvec_spinElt, coordY_spinElt_zero, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, smul_add]
  module

theorem spinElt_comp_yvec (c₁ m₁ : Fin 3 → K) (g₁ : Matrix (Fin 3) (Fin 3) K)
    (c₂ m₂ : Fin 3 → K) (g₂ : Matrix (Fin 3) (Fin 3) K) (v : Fin (2 * 4) → K) :
    yvec K (spinElt K c₁ m₁ g₁ (spinElt K c₂ m₂ g₂ v)) =
      ((g₁ * g₂).adjugate)ᵀ *ᵥ yvec K v +
        altMat K (m₁ + g₁ *ᵥ m₂) *ᵥ ((g₁ * g₂) *ᵥ xvec K v) +
        coordY K v 0 • (c₁ + (g₁.adjugate)ᵀ *ᵥ c₂ + altMat K (g₁ *ᵥ m₂) *ᵥ m₁) := by
  have e1 : (g₁.adjugate)ᵀ *ᵥ (altMat K m₂ *ᵥ (g₂ *ᵥ xvec K v)) =
      altMat K (g₁ *ᵥ m₂) *ᵥ ((g₁ * g₂) *ᵥ xvec K v) := by
    rw [← altMat_mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e2 : altMat K m₁ *ᵥ (g₁ *ᵥ m₂) = altMat K (g₁ *ᵥ m₂) *ᵥ m₁ := altMat_mulVec_comm _ _
  have e3 : g₁ *ᵥ (g₂ *ᵥ xvec K v) = (g₁ * g₂) *ᵥ xvec K v := Matrix.mulVec_mulVec _ _ _
  have e4 : (g₁.adjugate)ᵀ *ᵥ ((g₂.adjugate)ᵀ *ᵥ yvec K v) =
      ((g₁.adjugate)ᵀ * (g₂.adjugate)ᵀ) *ᵥ yvec K v := Matrix.mulVec_mulVec _ _ _
  rw [yvec_spinElt, yvec_spinElt, xvec_spinElt, coordY_spinElt_zero, contra_mul, altMat_add,
    Matrix.add_mulVec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e3, e4, e1, e2]
  module

end Comp

section CompZero

variable {K : Type} [Field K] [CharP K 2]

theorem spinElt_comp_coordX_zero (c₁ m₁ : Fin 3 → K) (g₁ : Matrix (Fin 3) (Fin 3) K)
    (hg₁ : g₁.det = 1) (c₂ m₂ : Fin 3 → K) (g₂ : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) :
    coordX K (spinElt K c₁ m₁ g₁ (spinElt K c₂ m₂ g₂ v)) 0 =
      coordX K (spinElt K (c₁ + (g₁.adjugate)ᵀ *ᵥ c₂ + altMat K (g₁ *ᵥ m₂) *ᵥ m₁)
        (m₁ + g₁ *ᵥ m₂) (g₁ * g₂) v) 0 := by
  have e1 : (g₁.adjugate)ᵀ *ᵥ (altMat K m₂ *ᵥ (g₂ *ᵥ xvec K v)) =
      altMat K (g₁ *ᵥ m₂) *ᵥ ((g₁ * g₂) *ᵥ xvec K v) := by
    rw [← altMat_mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e3 : g₁ *ᵥ (g₂ *ᵥ xvec K v) = (g₁ * g₂) *ᵥ xvec K v := Matrix.mulVec_mulVec _ _ _
  have e4 : (g₁.adjugate)ᵀ *ᵥ ((g₂.adjugate)ᵀ *ᵥ yvec K v) =
      ((g₁.adjugate)ᵀ * (g₂.adjugate)ᵀ) *ᵥ yvec K v := Matrix.mulVec_mulVec _ _ _
  have F1 : ((g₁.adjugate)ᵀ *ᵥ c₂) ⬝ᵥ ((g₁ * g₂) *ᵥ xvec K v) = c₂ ⬝ᵥ (g₂ *ᵥ xvec K v) := by
    rw [← e3, dot_contra_mulVec g₁ hg₁]
  have F2 : (g₁ *ᵥ m₂) ⬝ᵥ (((g₁.adjugate)ᵀ * (g₂.adjugate)ᵀ) *ᵥ yvec K v) =
      m₂ ⬝ᵥ ((g₂.adjugate)ᵀ *ᵥ yvec K v) := by
    rw [← e4, dotProduct_comm, dot_contra_mulVec g₁ hg₁, dotProduct_comm]
  have F3 : ((g₁.adjugate)ᵀ *ᵥ c₂) ⬝ᵥ (g₁ *ᵥ m₂) = c₂ ⬝ᵥ m₂ := dot_contra_mulVec g₁ hg₁ _ _
  have F4 : m₁ ⬝ᵥ (altMat K (g₁ *ᵥ m₂) *ᵥ ((g₁ * g₂) *ᵥ xvec K v)) =
      (altMat K (g₁ *ᵥ m₂) *ᵥ m₁) ⬝ᵥ ((g₁ * g₂) *ᵥ xvec K v) := by
    rw [dot_altMat_mulVec_comm, dotProduct_comm, altMat_mulVec_comm]
  have F5 : (altMat K (g₁ *ᵥ m₂) *ᵥ m₁) ⬝ᵥ m₁ = 0 := by
    rw [dotProduct_comm, altMat_mulVec_comm, dot_altMat_self]
  have F6 : (altMat K (g₁ *ᵥ m₂) *ᵥ m₁) ⬝ᵥ (g₁ *ᵥ m₂) = 0 := by
    rw [dotProduct_comm, dot_altMat_self]
  have F7 : m₁ ⬝ᵥ ((g₁.adjugate)ᵀ *ᵥ c₂) = ((g₁.adjugate)ᵀ *ᵥ c₂) ⬝ᵥ m₁ := dotProduct_comm _ _
  rw [coordX_spinElt_zero, coordX_spinElt_zero, coordX_spinElt_zero, xvec_spinElt, yvec_spinElt,
    coordY_spinElt_zero]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_eq_mul, e3, e4, e1, F1, F2, F3, F4, F5, F6, F7,
    contra_mul]
  ring

end CompZero

section Group

variable {K : Type} [Field K] [CharP K 2]

theorem spinElt_comp (c₁ m₁ : Fin 3 → K) (g₁ : Matrix (Fin 3) (Fin 3) K) (hg₁ : g₁.det = 1)
    (c₂ m₂ : Fin 3 → K) (g₂ : Matrix (Fin 3) (Fin 3) K) (v : Fin (2 * 4) → K) :
    spinElt K c₁ m₁ g₁ (spinElt K c₂ m₂ g₂ v) =
      spinElt K (c₁ + (g₁.adjugate)ᵀ *ᵥ c₂ + altMat K (g₁ *ᵥ m₂) *ᵥ m₁) (m₁ + g₁ *ᵥ m₂)
        (g₁ * g₂) v := by
  apply vec_ext
  · intro k
    refine Fin.cases (spinElt_comp_coordX_zero c₁ m₁ g₁ hg₁ c₂ m₂ g₂ v) (fun j => ?_) k
    show xvec K _ j = xvec K _ j
    rw [spinElt_comp_xvec, xvec_spinElt]
  · intro k
    refine Fin.cases (by rw [coordY_spinElt_zero, coordY_spinElt_zero, coordY_spinElt_zero])
      (fun j => ?_) k
    show yvec K _ j = yvec K _ j
    rw [spinElt_comp_yvec, yvec_spinElt]

omit [CharP K 2] in
theorem spinElt_one (v : Fin (2 * 4) → K) : spinElt K 0 0 1 v = v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [coordX_spinElt_zero]
      simp
    · show xvec K _ j = xvec K v j
      rw [xvec_spinElt]
      simp
  · intro k
    refine Fin.cases (coordY_spinElt_zero _ _ _ _) (fun j => ?_) k
    show yvec K _ j = yvec K v j
    rw [yvec_spinElt]
    simp [altMat_zero]

end Group

section Inj

variable {K : Type} [Field K]

theorem xvec_frameE_succ (j : Fin 3) : xvec K (frameE K j.succ) = Pi.single j 1 := by
  ext i
  unfold xvec
  rw [coordX_frameE, Pi.single_apply]
  simp [Fin.succ_inj, eq_comm]

theorem yvec_frameE (k : Fin 4) : yvec K (frameE K k) = 0 := by
  ext i
  unfold yvec
  rw [coordY_frameE]
  rfl

theorem xvec_frameF (k : Fin 4) : xvec K (frameF K k) = 0 := by
  ext i
  unfold xvec
  rw [coordX_frameF]
  rfl

theorem yvec_frameF_zero : yvec K (frameF K 0) = 0 := by
  ext i
  unfold yvec
  rw [coordY_frameF, if_neg (Fin.succ_ne_zero i).symm]
  rfl

theorem spinElt_injective {c m c' m' : Fin 3 → K} {g g' : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ v, spinElt K c m g v = spinElt K c' m' g' v) : c = c' ∧ m = m' ∧ g = g' := by
  have hg : g = g' := by
    ext i j
    have hj := congrFun (congrArg (xvec K) (h (frameE K j.succ))) i
    rw [xvec_spinElt, xvec_spinElt, xvec_frameE_succ, coordY_frameE] at hj
    simpa [Matrix.mulVec_single_one] using hj
  have h0 := h (frameF K 0)
  have hm : m = m' := by
    have := congrArg (xvec K) h0
    rw [xvec_spinElt, xvec_spinElt, xvec_frameF, coordY_frameF, if_pos rfl] at this
    simpa using this
  refine ⟨?_, hm, hg⟩
  have := congrArg (yvec K) h0
  rw [yvec_spinElt, yvec_spinElt, xvec_frameF, yvec_frameF_zero, coordY_frameF, if_pos rfl] at this
  simpa using this

end Inj

end CFSG.LieType.SpinGeom
