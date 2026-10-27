module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneODet

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL compInd)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def e4 (hd : 4 ≤ d) : Fin 4 ⊕ Fin (d - 4) ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem e4_inl (hd : 4 ≤ d) (i : Fin 4) : e4 hd (.inl i) = ⟨i, by omega⟩ :=
  Fin.ext (by simp [e4])

theorem e4_inr (hd : 4 ≤ d) (j : Fin (d - 4)) : e4 hd (.inr j) = ⟨4 + j, by omega⟩ :=
  Fin.ext (by simp [e4])

@[expose] def wSet : Finset (Fin d) :=
  Finset.univ.filter fun i => (i : ℕ) < 4

theorem mem_wSet (i : Fin d) : i ∈ (wSet : Finset (Fin d)) ↔ (i : ℕ) < 4 := by
  simp [wSet]

theorem e4_symm_of_lt (hd : 4 ≤ d) {i : Fin d} (hi : (i : ℕ) < 4) :
    (e4 hd).symm i = .inl ⟨i, hi⟩ := by
  rw [Equiv.symm_apply_eq, e4_inl]

theorem e4_symm_of_ge (hd : 4 ≤ d) {i : Fin d} (hi : 4 ≤ (i : ℕ)) :
    (e4 hd).symm i = .inr ⟨i - 4, by omega⟩ := by
  rw [Equiv.symm_apply_eq, e4_inr]
  ext
  simp
  omega

variable (K) in
@[expose] def embed4 (hd : 4 ≤ d) (X : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin d) (Fin d) K :=
  reindexAlgEquiv K K (e4 hd) (fromBlocks X 0 0 1)

theorem embed4_one (hd : 4 ≤ d) : embed4 K hd 1 = 1 := by
  rw [embed4, fromBlocks_one, map_one]

theorem embed4_mul (hd : 4 ≤ d) (X Y : Matrix (Fin 4) (Fin 4) K) :
    embed4 K hd (X * Y) = embed4 K hd X * embed4 K hd Y := by
  rw [embed4, embed4, embed4, ← map_mul, fromBlocks_multiply]
  simp

theorem embed4_apply_lt (hd : 4 ≤ d) (X : Matrix (Fin 4) (Fin 4) K) {i j : Fin d}
    (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4) : embed4 K hd X i j = X ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [embed4, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, e4_symm_of_lt hd hi,
    e4_symm_of_lt hd hj, fromBlocks_apply₁₁]

theorem embed4_apply_of (hd : 4 ≤ d) (X : Matrix (Fin 4) (Fin 4) K) {i j : Fin d}
    (hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) : embed4 K hd X i j = if i = j then 1 else 0 := by
  rw [embed4, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  rcases Nat.lt_or_ge (i : ℕ) 4 with hi | hi <;> rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
  · omega
  · have hne : i ≠ j := fun h => by rw [h] at hi; omega
    rw [e4_symm_of_lt hd hi, e4_symm_of_ge hd hj, fromBlocks_apply₁₂, Matrix.zero_apply]
    simp [hne]
  · have hne : i ≠ j := fun h => by rw [h] at hi; omega
    rw [e4_symm_of_ge hd hi, e4_symm_of_lt hd hj, fromBlocks_apply₂₁, Matrix.zero_apply]
    simp [hne]
  · rw [e4_symm_of_ge hd hi, e4_symm_of_ge hd hj, fromBlocks_apply₂₂, one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have hne : (⟨(i : ℕ) - 4, by omega⟩ : Fin (d - 4)) ≠ ⟨(j : ℕ) - 4, by omega⟩ := by
        intro h'
        apply h
        ext
        have := congrArg Fin.val h'
        simp at this
        omega
      simp [h, hne]

theorem embed4_injective (hd : 4 ≤ d) : Function.Injective (embed4 K hd) := by
  intro X Y h
  ext i j
  have := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  rwa [embed4_apply_lt hd X (by simp) (by simp), embed4_apply_lt hd Y (by simp) (by simp)] at this

variable (K) in
@[expose] def embedGL4 (hd : 4 ≤ d) : GL (Fin 4) K →* GL (Fin d) K where
  toFun X := ⟨embed4 K hd X, embed4 K hd (X⁻¹ : GL (Fin 4) K), by
      rw [← embed4_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, embed4_one], by
      rw [← embed4_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, embed4_one]⟩
  map_one' := Units.ext (by simp [embed4_one])
  map_mul' X Y := Units.ext (by simp [embed4_mul])

theorem coe_embedGL4 (hd : 4 ≤ d) (X : GL (Fin 4) K) :
    ((embedGL4 K hd X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = embed4 K hd X := rfl

theorem embedGL4_injective (hd : 4 ≤ d) : Function.Injective (embedGL4 K hd) := by
  intro X Y h
  apply Units.ext
  exact embed4_injective hd (congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h)

theorem embed4_support (hd : 4 ≤ d) (X : Matrix (Fin 4) (Fin 4) K) :
    ∀ i j, (i ∉ (wSet : Finset (Fin d)) ∨ j ∉ (wSet : Finset (Fin d))) →
      embed4 K hd X i j = if i = j then 1 else 0 := by
  intro i j hij
  apply embed4_apply_of
  simp only [mem_wSet, not_lt] at hij
  exact hij

theorem diagonal_eq_embed (hd : 4 ≤ d) {w : Fin d → K} {α a : K}
    (hw4 : ∀ i : Fin 4, w ⟨i, by omega⟩ = α * qW a i) :
    diagonal w = reindexAlgEquiv K K (e4 hd)
      (fromBlocks (α • diagonal (qW a)) 0 0 (diagonal fun j => w (e4 hd (.inr j)))) := by
  ext i j
  rw [coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  rcases Nat.lt_or_ge (i : ℕ) 4 with hi | hi <;> rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
  · rw [e4_symm_of_lt hd hi, e4_symm_of_lt hd hj, fromBlocks_apply₁₁, Matrix.smul_apply]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, diagonal_apply_eq, smul_eq_mul, ← hw4]
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne, smul_zero]
      intro h
      apply hij
      ext
      have := congrArg Fin.val h
      simpa using this
  · rw [e4_symm_of_lt hd hi, e4_symm_of_ge hd hj, fromBlocks_apply₁₂, Matrix.zero_apply,
      diagonal_apply_ne]
    intro h
    rw [h] at hi
    omega
  · rw [e4_symm_of_ge hd hi, e4_symm_of_lt hd hj, fromBlocks_apply₂₁, Matrix.zero_apply,
      diagonal_apply_ne]
    intro h
    rw [h] at hi
    omega
  · rw [e4_symm_of_ge hd hi, e4_symm_of_ge hd hj, fromBlocks_apply₂₂]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, diagonal_apply_eq, e4_inr]
      congr 1
      ext
      simp
      omega
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne]
      intro h
      apply hij
      ext
      have h' := congrArg Fin.val h
      simp at h'
      omega

theorem embedGL4_mem_iso (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K}
    (ha : a ≠ 0) (hw4 : ∀ i : Fin 4, w ⟨i, by omega⟩ = α * qW a i) {X : GL (Fin 4) K}
    (hX : X ∈ CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))) :
    embedGL4 K hd X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := by
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL, coe_embedGL4]
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL] at hX
  have ht : (reindexAlgEquiv K K (e4 hd) (fromBlocks (X : Matrix (Fin 4) (Fin 4) K) 0 0 1))ᵀ =
      reindexAlgEquiv K K (e4 hd) (fromBlocks (X : Matrix (Fin 4) (Fin 4) K) 0 0 1)ᵀ := by
    rw [coe_reindexAlgEquiv, transpose_reindex]
  rw [diagonal_eq_embed hd hw4, embed4, ht, ← map_mul, ← map_mul, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hX, smul_zero]

theorem transpose_reindexAlg (hd : 4 ≤ d) (M : Matrix (Fin 4 ⊕ Fin (d - 4))
    (Fin 4 ⊕ Fin (d - 4)) K) :
    (reindexAlgEquiv K K (e4 hd) M)ᵀ = reindexAlgEquiv K K (e4 hd) Mᵀ := by
  rw [coe_reindexAlgEquiv]
  exact transpose_reindex _ _ _

@[expose] def blk4 (hd : 4 ≤ d) (h : Matrix (Fin d) (Fin d) K) : Matrix (Fin 4) (Fin 4) K :=
  ((reindexAlgEquiv K K (e4 hd)).symm h).toBlocks₁₁

theorem blk4_apply (hd : 4 ≤ d) (h : Matrix (Fin d) (Fin d) K) (i j : Fin 4) :
    blk4 hd h i j = h ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  rw [blk4, toBlocks₁₁, of_apply, symm_reindexAlgEquiv, coe_reindexAlgEquiv, reindex_apply,
    submatrix_apply, Equiv.symm_symm, e4_inl, e4_inl]

theorem eq_reindex_fromBlocks (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {h : Matrix (Fin d) (Fin d) K}
    (hc : h * embed4 K hd (-1) = embed4 K hd (-1) * h) :
    h = reindexAlgEquiv K K (e4 hd) (fromBlocks (blk4 hd h) 0 0
      ((reindexAlgEquiv K K (e4 hd)).symm h).toBlocks₂₂) := by
  set h' := (reindexAlgEquiv K K (e4 hd)).symm h with hh'
  have hc' : h' * fromBlocks (-1) 0 0 1 = fromBlocks (-1) 0 0 1 * h' := by
    have e := congrArg (reindexAlgEquiv K K (e4 hd)).symm hc
    rw [embed4, map_mul, map_mul, AlgEquiv.symm_apply_apply] at e
    exact e
  have h12 : h'.toBlocks₁₂ = 0 := by
    have e := congrArg toBlocks₁₂ hc'
    conv_lhs at e => rw [← fromBlocks_toBlocks h']
    conv_rhs at e => rw [← fromBlocks_toBlocks h']
    rw [fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₁₂,
      toBlocks_fromBlocks₁₂] at e
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.neg_mul, Matrix.one_mul,
      Matrix.zero_mul, add_zero] at e
    ext i j
    have := congrFun (congrFun e i) j
    simp only [Matrix.neg_apply] at this
    have : (2 : K) * h'.toBlocks₁₂ i j = 0 := by linear_combination this
    exact (mul_eq_zero.1 this).resolve_left h2
  have h21 : h'.toBlocks₂₁ = 0 := by
    have e := congrArg toBlocks₂₁ hc'
    conv_lhs at e => rw [← fromBlocks_toBlocks h']
    conv_rhs at e => rw [← fromBlocks_toBlocks h']
    rw [fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₁] at e
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.one_mul,
      Matrix.zero_mul, add_zero, Matrix.mul_neg] at e
    ext i j
    have := congrFun (congrFun e i) j
    simp only [Matrix.neg_apply] at this
    have : (2 : K) * h'.toBlocks₂₁ i j = 0 := by linear_combination -this
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [blk4, ← hh', ← h12, ← h21, fromBlocks_toBlocks, hh', AlgEquiv.apply_symm_apply]

theorem mul_embed4_mul (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {h hi : Matrix (Fin d) (Fin d) K}
    (hh : h * hi = 1) (hc : h * embed4 K hd (-1) = embed4 K hd (-1) * h)
    (hci : hi * embed4 K hd (-1) = embed4 K hd (-1) * hi) (X : Matrix (Fin 4) (Fin 4) K) :
    h * embed4 K hd X * hi = embed4 K hd (blk4 hd h * X * blk4 hd hi) ∧
      blk4 hd h * blk4 hd hi = 1 := by
  have e1 := eq_reindex_fromBlocks h2 hd hc
  have e2 := eq_reindex_fromBlocks h2 hd hci
  set A := blk4 hd h
  set A' := blk4 hd hi
  set B := ((reindexAlgEquiv K K (e4 hd)).symm h).toBlocks₂₂
  set B' := ((reindexAlgEquiv K K (e4 hd)).symm hi).toBlocks₂₂
  have hprod : fromBlocks (A * A') 0 0 (B * B') = (1 : Matrix (Fin 4 ⊕ Fin (d - 4))
      (Fin 4 ⊕ Fin (d - 4)) K) := by
    have e := hh
    rw [e1, e2, ← map_mul, fromBlocks_multiply] at e
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e
    apply (reindexAlgEquiv K K (e4 hd)).injective
    rw [e, map_one]
  rw [← fromBlocks_one, fromBlocks_inj] at hprod
  refine ⟨?_, hprod.1⟩
  rw [e1, e2, embed4, embed4, ← map_mul, ← map_mul, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, hprod.2.2.2]

theorem blk4_embed4 (hd : 4 ≤ d) (X : Matrix (Fin 4) (Fin 4) K) : blk4 hd (embed4 K hd X) = X := by
  ext i j
  rw [blk4_apply, embed4_apply_lt hd X (by simp) (by simp)]

theorem blk4_isometry (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K} {α a : K} (hα : α ≠ 0)
    (hw4 : ∀ i : Fin 4, w ⟨i, by omega⟩ = α * qW a i) {h : Matrix (Fin d) (Fin d) K}
    (hc : h * embed4 K hd (-1) = embed4 K hd (-1) * h)
    (hiso : hᵀ * diagonal w * h = diagonal w) :
    (blk4 hd h)ᵀ * diagonal (qW a) * blk4 hd h = diagonal (qW a) := by
  have e1 := eq_reindex_fromBlocks h2 hd hc
  rw [e1, diagonal_eq_embed hd hw4, transpose_reindexAlg, ← map_mul, ← map_mul,
    fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hiso
  have := congrArg toBlocks₁₁ ((reindexAlgEquiv K K (e4 hd)).injective hiso)
  simp only [toBlocks_fromBlocks₁₁, transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_smul, Matrix.smul_mul] at this
  have h' : α • ((blk4 hd h)ᵀ * diagonal (qW a) * blk4 hd h) = α • diagonal (qW a) := this
  rw [← sub_eq_zero, ← smul_sub, smul_eq_zero] at h'
  exact sub_eq_zero.1 (h'.resolve_left hα)

end CFSG.ComponentClassification.Burgoyne.O
