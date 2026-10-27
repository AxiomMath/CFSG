module

public import CFSG.GH74.Generic.S1.UniPaired

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

noncomputable def tauVec (h : UnitaryFieldData p f F) (g₁ : Matrix (Fin 4) (Fin 4) F) (x : Fin 4 → F) : Fin 4 → F :=
  g₁ *ᵥ fun i => h.bar (x i)

theorem bar_mulVec (h : UnitaryFieldData p f F) (M : Matrix (Fin 4) (Fin 4) F) (x : Fin 4 → F) :
    (fun i => h.bar ((M *ᵥ x) i)) = M.map h.bar *ᵥ fun i => h.bar (x i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem exists_fixed_basis (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {g₁ : Matrix (Fin 4) (Fin 4) F}
    (hg₁ : g₁ * g₁.map h.bar = 1) :
    ∃ P₀ : Matrix (Fin 4) (Fin 4) F, IsUnit P₀.det ∧ g₁ * P₀.map h.bar = P₀ := by
  classical
  set τ : (Fin 4 → F) → (Fin 4 → F) := tauVec h g₁ with hτ
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    simp only [hτ, tauVec]
    rw [bar_mulVec, show (fun i => h.bar (h.bar (x i))) = x from funext fun i => h.bar_bar _,
      Matrix.mulVec_mulVec, hg₁, Matrix.one_mulVec]
  have hτadd : ∀ x y, τ (x + y) = τ x + τ y := by
    intro x y
    simp only [hτ, tauVec]
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  have hτsmul : ∀ (c : F) x, τ (c • x) = h.bar c • τ x := by
    intro c x
    simp only [hτ, tauVec]
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hτsub : ∀ x y, τ (x - y) = τ x - τ y := by
    intro x y
    have := hτadd (x - y) y
    rw [sub_add_cancel] at this
    exact eq_sub_of_add_eq this.symm
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have ht0 : c₀ - h.bar c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  set t : F := c₀ - h.bar c₀ with ht
  have hbt : h.bar t = -t := by rw [ht, map_sub, h.bar_bar, neg_sub]
  have hfin : Finite F := h.finite
  set Sset : Set (Fin 4 → F) := {x | τ x = x} with hS
  have hspan : Submodule.span F Sset = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hw1 : v + τ v ∈ Sset := by
      show τ (v + τ v) = v + τ v
      rw [hτadd, hττ, add_comm]
    have hw2 : t • (v - τ v) ∈ Sset := by
      show τ (t • (v - τ v)) = t • (v - τ v)
      rw [hτsmul, hτsub, hττ, hbt, neg_smul, ← smul_neg, neg_sub]
    have hv : v = (2 : F)⁻¹ • ((v + τ v) + t⁻¹ • (t • (v - τ v))) := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul, add_add_sub_cancel, ← two_smul F v, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span hw1)
      (Submodule.smul_mem _ _ (Submodule.subset_span hw2)))
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent F Sset
  have : Fintype b := Fintype.ofFinite b
  let B : Module.Basis b F (Fin 4 → F) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  have hcard : Fintype.card b = 4 := by
    have := Module.finrank_eq_card_basis B
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e : b ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  refine ⟨Matrix.of fun i j => ((e.symm j : b) : Fin 4 → F) i, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    exact hbli.comp e.symm e.symm.injective
  · ext i j
    have hj : τ ((e.symm j : b) : Fin 4 → F) = ((e.symm j : b) : Fin 4 → F) := hbS (e.symm j).2
    have := congrFun hj i
    simpa [hτ, tauVec, Matrix.mulVec, dotProduct, Matrix.mul_apply] using this


theorem exists_fixedField_matrix (h : UnitaryFieldData p f F) {m n : Type} {T : Matrix m n F}
    (hT : T.map h.bar = T) : ∃ T' : Matrix m n h.fixedField, T'.map (h.fixedField.subtype) = T := by
  refine ⟨Matrix.of fun i j => ⟨T i j, h.mem_fixedField.2 (by simpa using congrFun (congrFun hT i) j)⟩, ?_⟩
  ext i j
  rfl

theorem map_fixedField_bar (h : UnitaryFieldData p f F) {m n : Type} (T' : Matrix m n h.fixedField) :
    (T'.map (h.fixedField.subtype)).map h.bar = T'.map (h.fixedField.subtype) := by
  ext i j
  exact h.mem_fixedField.1 (T' i j).2

theorem adapted_finish (h : UnitaryFieldData p f F) {g₁ : Matrix (Fin 4) (Fin 4) F} {ε : F}
    (P' : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F)
    (hG : cT h P' * P' = Matrix.fromBlocks 0 1 1 0)
    (hg : g₁ * P'.map h.bar = P' * Matrix.fromBlocks 1 0 0 (ε • (1 : Matrix (Fin 2) (Fin 2) F))) :
    ∃ P : GL (Fin 4) F, cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat ∧
      g₁ * (P : Matrix (Fin 4) (Fin 4) F).map h.bar =
        (P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1) := by
  classical
  let Pm : Matrix (Fin 4) (Fin 4) F := P'.submatrix id e4.symm
  have hgram : cT h Pm * Pm = wMat := by
    have h1 : cT h Pm = (cT h P').submatrix e4.symm id := by
      ext i j
      simp [cT, Pm, Matrix.transpose_apply]
    change (cT h Pm) * (P'.submatrix id e4.symm) = wMat
    rw [h1, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hG]
    rw [wMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  have hdet : Pm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, det_wMat] at this
    have h5 : (cT h Pm).det = h.bar Pm.det := by
      rw [cT, Matrix.det_transpose]
      exact (RingHom.map_det (h.bar : F →+* F) Pm).symm
    rw [h5, h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mk'' Pm (isUnit_iff_ne_zero.2 hdet), hgram, ?_⟩
  change g₁ * Pm.map h.bar = Pm * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1)
  let Qd : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    Matrix.fromBlocks 1 0 0 (ε • (1 : Matrix (Fin 2) (Fin 2) F))
  have h1 : g₁ * Pm.map h.bar = (g₁ * P'.map h.bar).submatrix id e4.symm := rfl
  have h2' : Pm * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1) = (P' * Qd).submatrix id e4.symm := by
    rw [blk4_eq_reindex, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
    exact Matrix.submatrix_mul_equiv P' Qd id e4.symm e4.symm
  rw [h1, h2', hg]
  rfl


theorem gram_bar (h : UnitaryFieldData p f F) {g₁ P₀ : Matrix (Fin 4) (Fin 4) F} {ε : F}
    (hε : ε = 1 ∨ ε = -1) (hu : cT h g₁ * g₁ = ε • (1 : Matrix (Fin 4) (Fin 4) F))
    (hP : g₁ * P₀.map h.bar = P₀) :
    (cT h P₀ * P₀).map h.bar = ε • (cT h P₀ * P₀) ∧ (cT h P₀ * P₀)ᵀ = ε • (cT h P₀ * P₀) := by
  have hεε : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  have e1 : cT h P₀ * P₀ = ε • ((cT h P₀).map h.bar * P₀.map h.bar) := by
    have e : cT h P₀ * P₀ = cT h (g₁ * P₀.map h.bar) * (g₁ * P₀.map h.bar) := by rw [hP]
    rw [e, cT_mul]
    have e2 : cT h (P₀.map h.bar) = (cT h P₀).map h.bar := by
      simp [cT, Matrix.transpose_map]
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (cT h g₁) g₁, hu, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul]
  have e3 : (cT h P₀ * P₀).map h.bar = (cT h P₀).map h.bar * P₀.map h.bar := Matrix.map_mul
  rw [← e3] at e1
  have hb : (cT h P₀ * P₀).map h.bar = ε • (cT h P₀ * P₀) := by
    conv_rhs => rw [e1]
    rw [smul_smul, hεε, one_smul]
  refine ⟨hb, ?_⟩
  have hsym : cT h (cT h P₀ * P₀) = cT h P₀ * P₀ := by rw [cT_mul, cT_cT]
  rw [cT_def, hb, Matrix.transpose_smul] at hsym
  calc (cT h P₀ * P₀)ᵀ = (ε * ε) • (cT h P₀ * P₀)ᵀ := by rw [hεε, one_smul]
    _ = ε • (ε • (cT h P₀ * P₀)ᵀ) := (smul_smul _ _ _).symm
    _ = ε • (cT h P₀ * P₀) := by rw [hsym]


theorem det_gram_square (h : UnitaryFieldData p f F) {g P₀ : Matrix (Fin 4) (Fin 4) F}
    (hP : g * P₀.map h.bar = P₀)
    (hu : ∃ u : F, u ^ (p ^ f + 1) = 1 ∧ u * u = g.det) :
    ∃ s₀ : h.fixedField, (s₀ : F) * s₀ = (cT h P₀ * P₀).det := by
  obtain ⟨u, hu1, hu2⟩ := hu
  have hdetcT : ∀ M : Matrix (Fin 4) (Fin 4) F, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : F →+* F) M).symm
  set δ := P₀.det with hδ
  have hδ1 : g.det * h.bar δ = δ := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, show (P₀.map h.bar).det = h.bar δ from
      (RingHom.map_det (h.bar : F →+* F) P₀).symm] at this
    exact this
  have hnorm : h.norm u = 1 := by rw [h.norm_eq_pow, hu1]
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hnorm
  have hbr0 : h.bar r ≠ 0 := (map_ne_zero h.bar).2 hr0
  have hu_eq : u * h.bar r = r := by rw [← hr]; field_simp
  have hc : h.bar (δ / r ^ 2) = δ / r ^ 2 := by
    rw [map_div₀, map_pow]
    have hδ2 : δ * h.bar r ^ 2 = h.bar δ * r ^ 2 := by
      have : δ = u * u * h.bar δ := by rw [hu2, hδ1]
      calc δ * h.bar r ^ 2 = u * u * h.bar δ * h.bar r ^ 2 := by rw [← this]
        _ = h.bar δ * (u * h.bar r) ^ 2 := by ring
        _ = h.bar δ * r ^ 2 := by rw [hu_eq]
    field_simp
    linear_combination -hδ2
  refine ⟨⟨δ / r ^ 2 * h.norm r, ?_⟩, ?_⟩
  · refine Subfield.mul_mem _ (h.mem_fixedField.2 hc) (h.norm_mem_fixedField r)
  · show (δ / r ^ 2 * h.norm r) * (δ / r ^ 2 * h.norm r) = (cT h P₀ * P₀).det
    rw [Matrix.det_mul, hdetcT, ← hδ]
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    have hbδ : h.bar δ = δ / r ^ 2 * h.bar r ^ 2 := by
      have hc' : h.bar δ / h.bar r ^ 2 = δ / r ^ 2 := by
        simpa only [map_div₀, map_pow] using hc
      rw [div_eq_iff (pow_ne_zero 2 hbr0)] at hc'
      exact hc'
    have hδr : δ = δ / r ^ 2 * r ^ 2 := by field_simp
    calc δ / r ^ 2 * h.norm r * (δ / r ^ 2 * h.norm r)
        = (δ / r ^ 2 * h.bar r ^ 2) * (δ / r ^ 2 * r ^ 2) := by rw [UnitaryFieldData.norm]; ring
      _ = h.bar δ * δ := by rw [← hbδ, ← hδr]

end CFSG.GH74.Generic.S1.Uni
