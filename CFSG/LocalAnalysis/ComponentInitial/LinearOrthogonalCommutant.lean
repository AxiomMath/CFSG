module

public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module Matrix QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

section Triple

variable (B : LinearMap.BilinForm k V) (u : Fin 3 → V) (a : k)

@[expose] def orthoTripleCoord : V →ₗ[k] (Fin 3 → k) :=
  a⁻¹ • LinearMap.pi fun i => B.flip (u i)

theorem orthoTripleCoord_apply (x : V) (i : Fin 3) :
    orthoTripleCoord B u a x i = a⁻¹ * B x (u i) :=
  rfl

@[expose] def orthoTripleEnd (M : Matrix (Fin 3) (Fin 3) k) : Module.End k V :=
  LinearMap.id + Fintype.linearCombination k u ∘ₗ (M - 1).mulVecLin ∘ₗ orthoTripleCoord B u a

theorem orthoTripleEnd_apply (M : Matrix (Fin 3) (Fin 3) k) (x : V) :
    orthoTripleEnd B u a M x =
      x + ∑ j, ((M - 1) *ᵥ orthoTripleCoord B u a x) j • u j := by
  simp only [orthoTripleEnd, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Matrix.mulVecLin_apply, Fintype.linearCombination_apply]

variable {B u a}

theorem orthoTripleCoord_linearCombination (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0)
    (ha : a ≠ 0) (c : Fin 3 → k) :
    orthoTripleCoord B u a (Fintype.linearCombination k u c) = c := by
  funext i
  simp [orthoTripleCoord_apply, Fintype.linearCombination_apply, map_sum, hu]
  field_simp

theorem orthoTripleEnd_one : orthoTripleEnd B u a 1 = 1 := by
  ext x
  simp [orthoTripleEnd_apply]

theorem orthoTripleEnd_mul (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0)
    (ha : a ≠ 0) (M N : Matrix (Fin 3) (Fin 3) k) :
    orthoTripleEnd B u a (M * N) = orthoTripleEnd B u a M * orthoTripleEnd B u a N := by
  ext x
  have h := orthoTripleCoord_linearCombination hu ha
  simp only [orthoTripleEnd, Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, Matrix.mulVecLin_apply, map_add, h]
  rw [add_assoc, ← map_add, ← map_add]
  congr 2
  rw [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec]
  congr 1
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  abel

theorem mulVec_dotProduct_mulVec_of_transpose_mul {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Mᵀ * M = 1) (c d : Fin 3 → k) : (M *ᵥ c) ⬝ᵥ (M *ᵥ d) = c ⬝ᵥ d := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hM, one_mulVec]

theorem orthoTripleEnd_isometry (hBs : B.IsSymm)
    (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0) (ha : a ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) k} (hM : Mᵀ * M = 1) (x y : V) :
    B (orthoTripleEnd B u a M x) (orthoTripleEnd B u a M y) = B x y := by
  have F1 : ∀ (x : V) (c : Fin 3 → k),
      B x (Fintype.linearCombination k u c) = a * (orthoTripleCoord B u a x ⬝ᵥ c) := by
    intro x c
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, smul_eq_mul, dotProduct,
      orthoTripleCoord_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have F2 : ∀ (c : Fin 3 → k) (y : V),
      B (Fintype.linearCombination k u c) y = a * (c ⬝ᵥ orthoTripleCoord B u a y) := by
    intro c y
    rw [hBs.eq, F1, dotProduct_comm]
  have key : ∀ c d : Fin 3 → k, c ⬝ᵥ ((M - 1) *ᵥ d) + ((M - 1) *ᵥ c) ⬝ᵥ d +
      ((M - 1) *ᵥ c) ⬝ᵥ ((M - 1) *ᵥ d) = 0 := by
    intro c d
    simp only [sub_mulVec, one_mulVec, dotProduct_sub, sub_dotProduct,
      mulVec_dotProduct_mulVec_of_transpose_mul hM]
    ring
  simp only [orthoTripleEnd, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    mulVecLin_apply, map_add, LinearMap.add_apply, F1, F2,
    orthoTripleCoord_linearCombination hu ha]
  linear_combination a * key _ _

variable (B u a) in
@[expose] def orthoTripleHom (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0)
    (ha : a ≠ 0) : Matrix (Fin 3) (Fin 3) k →* Module.End k V where
  toFun := orthoTripleEnd B u a
  map_one' := orthoTripleEnd_one
  map_mul' := orthoTripleEnd_mul hu ha

variable (B u a) in
@[expose] def orthoTripleGL (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0)
    (ha : a ≠ 0) : GL (Fin 3) k →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    (Units.map (orthoTripleHom B u a hu ha))

theorem orthoTripleGL_apply (hu : ∀ i j, B (u i) (u j) = if i = j then a else 0)
    (ha : a ≠ 0) (M : GL (Fin 3) k) (x : V) :
    orthoTripleGL B u a hu ha M x = orthoTripleEnd B u a M x :=
  rfl

end Triple

section Matrices

variable (k)

@[expose] def tripleS0 : GL (Fin 3) k :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleS1 : GL (Fin 3) k :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, 1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleT01 : GL (Fin 3) k :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleT12 : GL (Fin 3) k :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleC : GL (Fin 3) k :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleD01 : GL (Fin 3) k :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleD12 : GL (Fin 3) k :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, -1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

@[expose] def tripleD02 : GL (Fin 3) k :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
    by simp [Matrix.one_fin_three], by simp [Matrix.one_fin_three]⟩

theorem commutator_tripleS0_tripleT01 : ⁅tripleS0 k, tripleT01 k⁆ = tripleD01 k :=
  Units.ext (by simp [commutatorElement_def, tripleS0, tripleT01, tripleD01])

theorem commutator_tripleS1_tripleT12 : ⁅tripleS1 k, tripleT12 k⁆ = tripleD12 k :=
  Units.ext (by simp [commutatorElement_def, tripleS1, tripleT12, tripleD12])

theorem tripleD01_mul_tripleD12 : tripleD01 k * tripleD12 k = tripleD02 k :=
  Units.ext (by simp [tripleD01, tripleD12, tripleD02])

theorem commutator_tripleT01_tripleT12 : ⁅tripleT01 k, tripleT12 k⁆ = tripleC k :=
  Units.ext (by simp [commutatorElement_def, tripleT01, tripleT12, tripleC])

theorem commutator_tripleD02_tripleC : ⁅tripleD02 k, tripleC k⁆ = tripleD01 k :=
  Units.ext (by simp [commutatorElement_def, tripleD02, tripleC, tripleD01])

theorem commutator_tripleD12_tripleC : ⁅tripleD12 k, tripleC k⁆ = tripleD02 k :=
  Units.ext (by simp [commutatorElement_def, tripleD12, tripleC, tripleD02])

theorem transpose_mul_tripleS0 :
    ((tripleS0 k : Matrix (Fin 3) (Fin 3) k))ᵀ * tripleS0 k = 1 := by
  change (!![(-1 : k), 0, 0; 0, 1, 0; 0, 0, 1])ᵀ * !![-1, 0, 0; 0, 1, 0; 0, 0, 1] = 1
  rw [Matrix.eta_fin_three (!![(-1 : k), 0, 0; 0, 1, 0; 0, 0, 1])ᵀ]
  simp [Matrix.one_fin_three]

theorem transpose_mul_tripleS1 :
    ((tripleS1 k : Matrix (Fin 3) (Fin 3) k))ᵀ * tripleS1 k = 1 := by
  change (!![(1 : k), 0, 0; 0, -1, 0; 0, 0, 1])ᵀ * !![1, 0, 0; 0, -1, 0; 0, 0, 1] = 1
  rw [Matrix.eta_fin_three (!![(1 : k), 0, 0; 0, -1, 0; 0, 0, 1])ᵀ]
  simp [Matrix.one_fin_three]

theorem transpose_mul_tripleT01 :
    ((tripleT01 k : Matrix (Fin 3) (Fin 3) k))ᵀ * tripleT01 k = 1 := by
  change (!![(0 : k), 1, 0; 1, 0, 0; 0, 0, 1])ᵀ * !![0, 1, 0; 1, 0, 0; 0, 0, 1] = 1
  rw [Matrix.eta_fin_three (!![(0 : k), 1, 0; 1, 0, 0; 0, 0, 1])ᵀ]
  simp [Matrix.one_fin_three]

theorem transpose_mul_tripleT12 :
    ((tripleT12 k : Matrix (Fin 3) (Fin 3) k))ᵀ * tripleT12 k = 1 := by
  change (!![(1 : k), 0, 0; 0, 0, 1; 0, 1, 0])ᵀ * !![1, 0, 0; 0, 0, 1; 0, 1, 0] = 1
  rw [Matrix.eta_fin_three (!![(1 : k), 0, 0; 0, 0, 1; 0, 1, 0])ᵀ]
  simp [Matrix.one_fin_three]

theorem map_tripleD_mem {G : Type*} [Group G] (φ : GL (Fin 3) k →* G) {O : Subgroup G}
    (h0 : φ (tripleS0 k) ∈ O) (h1 : φ (tripleS1 k) ∈ O) (h01 : φ (tripleT01 k) ∈ O)
    (h12 : φ (tripleT12 k) ∈ O) :
    φ (tripleD01 k) ∈ ⁅⁅O, O⁆, ⁅O, O⁆⁆ ∧ φ (tripleD02 k) ∈ ⁅⁅O, O⁆, ⁅O, O⁆⁆ := by
  have hD01 : φ (tripleD01 k) ∈ ⁅O, O⁆ := by
    rw [← commutator_tripleS0_tripleT01, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator h0 h01
  have hD12 : φ (tripleD12 k) ∈ ⁅O, O⁆ := by
    rw [← commutator_tripleS1_tripleT12, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator h1 h12
  have hD02 : φ (tripleD02 k) ∈ ⁅O, O⁆ := by
    rw [← tripleD01_mul_tripleD12, map_mul]
    exact Subgroup.mul_mem _ hD01 hD12
  have hC : φ (tripleC k) ∈ ⁅O, O⁆ := by
    rw [← commutator_tripleT01_tripleT12, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator h01 h12
  refine ⟨?_, ?_⟩
  · rw [← commutator_tripleD02_tripleC, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hD02 hC
  · rw [← commutator_tripleD12_tripleC, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hD12 hC

variable {k}

theorem orthoTripleEnd_tripleD01 (B : LinearMap.BilinForm k V) (u : Fin 3 → V) (a : k)
    (x : V) : orthoTripleEnd B u a (tripleD01 k) x =
      x - (2 * orthoTripleCoord B u a x 0) • u 0 - (2 * orthoTripleCoord B u a x 1) • u 1 := by
  rw [orthoTripleEnd_apply]
  simp [tripleD01, Fin.sum_univ_three, mulVec, dotProduct, Matrix.one_fin_three]
  module

theorem orthoTripleEnd_tripleD02 (B : LinearMap.BilinForm k V) (u : Fin 3 → V) (a : k)
    (x : V) : orthoTripleEnd B u a (tripleD02 k) x =
      x - (2 * orthoTripleCoord B u a x 0) • u 0 - (2 * orthoTripleCoord B u a x 2) • u 2 := by
  rw [orthoTripleEnd_apply]
  simp [tripleD02, Fin.sum_univ_three, mulVec, dotProduct, Matrix.one_fin_three]
  module

end Matrices

section Orthogonal

variable {Q : QuadraticForm k V}

theorem polarBilin_isSymm : LinearMap.BilinForm.IsSymm (polarBilin Q) :=
  LinearMap.BilinForm.isSymm_iff.mpr ⟨fun _ _ => polar_comm _ _ _⟩

theorem odd_natCard_of_ringChar_ne_two [Finite k] (hk : ringChar k ≠ 2) : Odd (Nat.card k) := by
  have := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact Nat.mod_two_ne_zero.mp fun h => hk (FiniteField.even_card_iff_char_two.mpr h)

theorem orthoTripleGL_mem_orthogonalGroup (h2 : (2 : k) ≠ 0) {u : Fin 3 → V} {a : k}
    (hu : ∀ i j, polarBilin Q (u i) (u j) = if i = j then a else 0) (ha : a ≠ 0)
    {M : GL (Fin 3) k} (hM : (M : Matrix (Fin 3) (Fin 3) k)ᵀ * M = 1) :
    orthoTripleGL (polarBilin Q) u a hu ha M ∈ orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  have h := orthoTripleEnd_isometry polarBilin_isSymm hu ha hM x x
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, two_smul,
    two_smul, ← two_mul, ← two_mul] at h
  exact mul_left_cancel₀ h2 h

theorem exists_mem_secondDerived_neg [Finite k] (hk : ringChar k ≠ 2) [FiniteDimensional k V]
    (hd : 4 ≤ finrank k V) (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : polar Q v v ≠ 0) :
    ∃ h₁ ∈ ⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆, ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆,
      ∃ h₂ ∈ ⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆, ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆,
        h₁ v = -v ∧ h₂ v = -v ∧ ∀ y, h₁ y = -y → h₂ y = -y → ∃ c : k, y = c • v := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨-, hbasis⟩ := finite_odd_symmetric_equal_value_orthogonal_basis
    (odd_natCard_of_ringChar_ne_two hk) rfl (by omega) hQ polarBilin_isSymm
  obtain ⟨e, heo, he0, hea, -⟩ := hbasis (polar Q v v) v hv rfl
  set a := polar Q v v with ha
  let u : Fin 3 → V := fun i => e (Fin.castLE (by omega) i)
  have hu : ∀ i j, polarBilin Q (u i) (u j) = if i = j then a else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact hea _ (by simp only [Fin.val_castLE]; omega)
    · exact heo fun h => hij (Fin.castLE_injective _ h)
  have hu0 : u 0 = v := he0 _ rfl
  have hmem : ∀ M : GL (Fin 3) k, (M : Matrix (Fin 3) (Fin 3) k)ᵀ * M = 1 →
      orthoTripleGL (polarBilin Q) u a hu hv M ∈ orthogonalGroup Q :=
    fun M hM => orthoTripleGL_mem_orthogonalGroup h2 hu hv hM
  obtain ⟨hD01, hD02⟩ := map_tripleD_mem k (orthoTripleGL (polarBilin Q) u a hu hv)
    (hmem _ (transpose_mul_tripleS0 k)) (hmem _ (transpose_mul_tripleS1 k))
    (hmem _ (transpose_mul_tripleT01 k)) (hmem _ (transpose_mul_tripleT12 k))
  have hc : ∀ i, orthoTripleCoord (polarBilin Q) u a v i = if 0 = i then 1 else 0 := by
    intro i
    rw [orthoTripleCoord_apply, ← hu0, hu]
    split_ifs
    · exact inv_mul_cancel₀ hv
    · exact mul_zero _
  refine ⟨_, hD01, _, hD02, ?_, ?_, fun y hy₁ hy₂ => ?_⟩
  · rw [orthoTripleGL_apply, orthoTripleEnd_tripleD01, hc, hc]
    simp only [↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, mul_one, mul_zero, zero_smul,
      sub_zero]
    rw [hu0]
    module
  · rw [orthoTripleGL_apply, orthoTripleEnd_tripleD02, hc, hc]
    simp only [↓reduceIte, mul_one, Fin.reduceEq, mul_zero, zero_smul, sub_zero]
    rw [hu0]
    module
  · rw [orthoTripleGL_apply, orthoTripleEnd_tripleD01] at hy₁
    rw [orthoTripleGL_apply, orthoTripleEnd_tripleD02] at hy₂
    have h1 : polarBilin Q y (u 1) = 0 := by
      have h := congrArg (fun z => polarBilin Q z (u 1)) hy₂
      simp only [map_sub, map_smul, map_neg, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.neg_apply, hu, smul_eq_mul] at h
      simp only [Fin.reduceEq, ↓reduceIte, mul_zero, sub_zero] at h
      have h' : (2 : k) * polarBilin Q y (u 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    rw [orthoTripleCoord_apply (polarBilin Q) u a y 1, h1, mul_zero, mul_zero, zero_smul,
      sub_zero, hu0] at hy₁
    refine ⟨orthoTripleCoord (polarBilin Q) u a y 0, ?_⟩
    have h : (2 : k) • (y - orthoTripleCoord (polarBilin Q) u a y 0 • v) = 0 := by
      linear_combination (norm := module) hy₁
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left h2)

theorem exists_basis_polar_one [Finite k] (hk : ringChar k ≠ 2) [FiniteDimensional k V]
    (hd : 2 ≤ finrank k V) (hQ : (polarBilin Q).Nondegenerate) :
    ∃ e : Basis (Fin (finrank k V)) k V, (polarBilin Q).IsOrthoᵢ e ∧
      (∀ i : Fin (finrank k V), (i : ℕ) < finrank k V - 1 → polar Q (e i) (e i) = 1) ∧
      ∀ i, polar Q (e i) (e i) ≠ 0 := by
  obtain ⟨hex, hbasis⟩ := finite_odd_symmetric_equal_value_orthogonal_basis
    (odd_natCard_of_ringChar_ne_two hk) rfl hd hQ polarBilin_isSymm
  obtain ⟨v, hv⟩ := hex 1 one_ne_zero
  obtain ⟨e, heo, -, hea, hel⟩ := hbasis 1 v one_ne_zero hv
  refine ⟨e, heo, hea, fun i => ?_⟩
  rcases Nat.lt_or_ge (i : ℕ) (finrank k V - 1) with h | h
  · rw [← polarBilin_apply_apply, hea i h]
    exact one_ne_zero
  · exact hel i (by omega)

theorem eq_zero_of_forall_polar_self_ne_zero [Finite k] (hk : ringChar k ≠ 2)
    [FiniteDimensional k V] (hd : 2 ≤ finrank k V) (hQ : (polarBilin Q).Nondegenerate)
    (f : V →ₗ[k] k) (hf : ∀ v, polar Q v v ≠ 0 → f v = 0) : f = 0 := by
  obtain ⟨e, -, -, hne⟩ := exists_basis_polar_one hk hd hQ
  exact e.ext fun i => by rw [hf _ (hne i), LinearMap.zero_apply]

theorem exists_eq_smul_of_forall_polar_ne_zero [Finite k] (hk : ringChar k ≠ 2)
    [FiniteDimensional k V] (hd : 3 ≤ finrank k V) (hQ : (polarBilin Q).Nondegenerate)
    (g : V →ₗ[k] V) (hg : ∀ v, polar Q v v ≠ 0 → ∃ c : k, g v = c • v) :
    ∃ c : k, ∀ v, g v = c • v := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨e, heo, he1, hne⟩ := exists_basis_polar_one hk (by omega) hQ
  choose l hl using fun i => hg (e i) (hne i)
  have ho : ∀ i j, i ≠ j → polarBilin Q (e i) (e j) = 0 := fun i j h => heo h
  have coeff : ∀ (s : Finset (Fin (finrank k V))) (c : Fin (finrank k V) → k) (j), j ∈ s →
      polarBilin Q (∑ i ∈ s, c i • e i) (e j) = c j * polar Q (e j) (e j) := by
    intro s c j hj
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho i j hij, mul_zero])
      (fun h => absurd hj h), polarBilin_apply_apply]
  have key : ∀ s : Finset (Fin (finrank k V)), ∑ i ∈ s, polar Q (e i) (e i) ≠ 0 →
      ∀ i ∈ s, ∀ j ∈ s, l i = l j := by
    intro s hs
    have hnorm : polar Q (∑ i ∈ s, e i) (∑ i ∈ s, e i) = ∑ i ∈ s, polar Q (e i) (e i) := by
      rw [← polarBilin_apply_apply, map_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have h := coeff s (fun _ => 1) j hj
      simp only [one_smul, one_mul] at h
      exact h
    obtain ⟨μ, hμ⟩ := hg _ (hnorm ▸ hs)
    have hμ' : ∑ i ∈ s, l i • e i = ∑ i ∈ s, μ • e i := by
      rw [← Finset.smul_sum, ← hμ, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hl i).symm
    have hlμ : ∀ j ∈ s, l j = μ := fun j hj => by
      have h := congrArg (fun z => polarBilin Q z (e j)) hμ'
      simp only [coeff s _ j hj] at h
      exact mul_right_cancel₀ (hne j) h
    intro i hi j hj
    rw [hlμ i hi, hlμ j hj]
  let i₀ : Fin (finrank k V) := ⟨0, by omega⟩
  let i₁ : Fin (finrank k V) := ⟨1, by omega⟩
  have hall : ∀ i, l i = l i₀ := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0]
    have hi0' : i₀ ≠ i := Ne.symm hi0
    have h1 : polar Q (e i₀) (e i₀) = 1 := he1 i₀ (by simp [i₀]; omega)
    rcases Nat.lt_or_ge (i : ℕ) (finrank k V - 1) with hi | hi
    · refine (key {i₀, i} ?_ i (by simp) i₀ (by simp))
      rw [Finset.sum_pair hi0', h1, he1 i hi, one_add_one_eq_two]
      exact h2
    · by_cases hb : 1 + polar Q (e i) (e i) = 0
      · have hi1 : i₁ ≠ i := fun h => by
          have := congrArg Fin.val h
          simp [i₁] at this
          omega
        have h01 : i₀ ≠ i₁ := fun h => by
          have := congrArg Fin.val h
          simp [i₀, i₁] at this
        refine (key {i₀, i₁, i} ?_ i (by simp) i₀ (by simp))
        rw [Finset.sum_insert (by simp [h01, hi0']), Finset.sum_pair hi1, h1,
          he1 i₁ (by simp [i₁]; omega), ← add_assoc, add_assoc 1 1, hb, add_zero]
        exact one_ne_zero
      · refine (key {i₀, i} ?_ i (by simp) i₀ (by simp))
        rw [Finset.sum_pair hi0', h1]
        exact hb
  refine ⟨l i₀, fun v => ?_⟩
  have hg' : g = l i₀ • LinearMap.id :=
    e.ext fun i => by rw [hl i, hall i, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hg', LinearMap.smul_apply, LinearMap.id_apply]

end Orthogonal

theorem odd_orthogonal_second_derived_natural_commutant [Finite k] (hk : ringChar k ≠ 2)
    [FiniteDimensional k V] (hd : 4 ≤ finrank k V) (Q : QuadraticForm k V)
    (hQ : (polarBilin Q).Nondegenerate) :
    (Subgroup.centralizer ((⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆,
        ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆ : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) :
        Set (V ≃ₗ[k] V)) =
      {g | ∃ a : kˣ, ∀ v, g v = (a : k) • v} ∧
    {v : V | ∀ g ∈ ⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆,
        ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆, g v = v} = {0} ∧
    ∀ f : Module.Dual k V, (∀ g ∈ ⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆,
        ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆, ∀ v, f (g v) = f v) → f = 0 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hDO : ⁅⁅orthogonalGroup Q, orthogonalGroup Q⁆, ⁅orthogonalGroup Q, orthogonalGroup Q⁆⁆ ≤
      orthogonalGroup Q :=
    (Subgroup.commutator_le_self _).trans (Subgroup.commutator_le_self _)
  refine ⟨Set.ext fun g => ⟨fun hg => ?_, ?_⟩, Set.ext fun x => ⟨fun hx => ?_, ?_⟩,
    fun f hf => ?_⟩
  ·
    have hline : ∀ v, polar Q v v ≠ 0 → ∃ c : k, (g : V →ₗ[k] V) v = c • v := by
      intro v hv
      obtain ⟨h₁, hh₁, h₂, hh₂, hv₁, hv₂, heig⟩ := exists_mem_secondDerived_neg hk hd hQ hv
      have hc₁ := Subgroup.mem_centralizer_iff.mp hg h₁ hh₁
      have hc₂ := Subgroup.mem_centralizer_iff.mp hg h₂ hh₂
      refine heig (g v) ?_ ?_
      · rw [← LinearEquiv.mul_apply, hc₁, LinearEquiv.mul_apply, hv₁, map_neg]
      · rw [← LinearEquiv.mul_apply, hc₂, LinearEquiv.mul_apply, hv₂, map_neg]
    obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_polar_ne_zero hk (by omega) hQ _ hline
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hc0 : c ≠ 0 := fun h => hv (g.injective (by
      rw [map_zero]
      exact (hc v).trans (by rw [h, zero_smul])))
    exact ⟨Units.mk0 c hc0, hc⟩
  · rintro ⟨a, ha⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h _ => LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, ha, map_smul]
  ·
    have hB : polarBilin Q x = 0 := by
      refine eq_zero_of_forall_polar_self_ne_zero hk (by omega) hQ _ fun v hv => ?_
      obtain ⟨h₁, hh₁, -, -, hv₁, -, -⟩ := exists_mem_secondDerived_neg hk hd hQ hv
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hDO hh₁) x v
      rw [hx h₁ hh₁, hv₁, polar_neg_right] at h
      rw [polarBilin_apply_apply]
      have h' : (2 : k) * polar Q x v = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left h2
    exact hQ.1 x fun y => by rw [hB, LinearMap.zero_apply]
  · rintro rfl g _
    exact map_zero g
  · refine eq_zero_of_forall_polar_self_ne_zero hk (by omega) hQ f fun v hv => ?_
    obtain ⟨h₁, hh₁, -, -, hv₁, -, -⟩ := exists_mem_secondDerived_neg hk hd hQ hv
    have h := hf h₁ hh₁ v
    rw [hv₁, map_neg] at h
    have h' : (2 : k) * f v = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2

end CFSG.LocalAnalysis.ComponentInitial
