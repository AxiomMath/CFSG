module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem det_one_sub_of_isNilpotent {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) :
    (1 - N).det = 1 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card (Fin n) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
  have h2 := Matrix.eval_charpoly N 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  exact h2.symm

theorem det_eq_one_of_sub_one_pow_three {M : Matrix (Fin n) (Fin n) K} (hM : (M - 1) ^ 3 = 0) :
    M.det = 1 := by
  have hN : IsNilpotent (1 - M) :=
    ⟨3, by rw [show (1 : Matrix (Fin n) (Fin n) K) - M = -(M - 1) by abel, neg_pow, hM, mul_zero]⟩
  rw [← det_one_sub_of_isNilpotent hN, sub_sub_cancel]

theorem eq_zero_of_forall_mulVec_eq_zero {N : Matrix (Fin n) (Fin n) K}
    (hN : ∀ v, N *ᵥ v = 0) : N = 0 := by
  ext i j
  have h1 := congrFun (hN (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at h1

theorem sub_one_pow_three_eq_zero {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) -
      (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) = 0) : (M - 1) ^ 3 = 0 := by
  refine eq_zero_of_forall_mulVec_eq_zero fun v => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [sub_mulVec, one_mulVec]
  exact hM v

@[expose] def unipotentGL (M : Matrix (Fin n) (Fin n) K) (hM : (M - 1) ^ 3 = 0) :
    GL (Fin n) K where
  val := M
  inv := 1 - (M - 1) + (M - 1) ^ 2
  val_inv := by
    have h1 : M * (1 - (M - 1) + (M - 1) ^ 2) = 1 + (M - 1) ^ 3 := by noncomm_ring
    rw [h1, hM, add_zero]
  inv_val := by
    have h1 : (1 - (M - 1) + (M - 1) ^ 2) * M = 1 + (M - 1) ^ 3 := by noncomm_ring
    rw [h1, hM, add_zero]

theorem coe_unipotentGL (M : Matrix (Fin n) (Fin n) K) (hM : (M - 1) ^ 3 = 0) :
    ((unipotentGL M hM : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M :=
  rfl

theorem pow_four_eq_one_of_sub_one_pow_three [CharP K 2] {M : Matrix (Fin n) (Fin n) K}
    (hM : (M - 1) ^ 3 = 0) : M ^ 4 = 1 := by
  have h2 : (2 : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [← Matrix.diagonal_ofNat, CharTwo.two_eq_zero, Matrix.diagonal_zero]
  have h1 : (1 + (M - 1)) ^ 4 = 1 + 2 * (2 * (M - 1) + 3 * (M - 1) ^ 2 + 2 * (M - 1) ^ 3) +
      (M - 1) ^ 3 * (M - 1) := by noncomm_ring
  rw [add_sub_cancel, h2, hM, zero_mul, zero_mul, add_zero, add_zero] at h1
  exact h1

section Eichler

variable (h : UnitaryFieldData p f K) (G : Matrix (Fin n) (Fin n) K)

@[expose] noncomputable def gramRow (w : Fin n → K) : Fin n → K :=
  (fun a => h.bar (w a)) ᵥ* G

theorem gramRow_dotProduct (w v : Fin n → K) : gramRow h G w ⬝ᵥ v = gramForm h G w v := by
  rw [gramRow, gramForm_apply, dotProduct_mulVec]

@[expose] noncomputable def eichlerMatrix (w y : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec y (gramRow h G w) - vecMulVec w (gramRow h G y) + c • vecMulVec w (gramRow h G w)

theorem eichlerMatrix_mulVec (w y : Fin n → K) (c : K) (v : Fin n → K) :
    eichlerMatrix h G w y c *ᵥ v =
      v + gramForm h G w v • y - gramForm h G y v • w + (c * gramForm h G w v) • w := by
  simp only [eichlerMatrix, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    gramRow_dotProduct, op_smul_eq_smul, smul_smul]

variable {h G}

theorem eichlerMatrix_isometry (hH : (gramForm h G).IsSymm) {w y : Fin n → K}
    (hww : gramForm h G w w = 0) (hwy : gramForm h G w y = 0) {c : K}
    (hc : c + h.bar c = -gramForm h G y y) (v v' : Fin n → K) :
    gramForm h G (eichlerMatrix h G w y c *ᵥ v) (eichlerMatrix h G w y c *ᵥ v') =
      gramForm h G v v' := by
  have hyw : gramForm h G y w = 0 := by rw [← hH.eq w y, hwy, map_zero]
  have hvy : gramForm h G v y = h.bar (gramForm h G y v) := (hH.eq y v).symm
  have hvw : gramForm h G v w = h.bar (gramForm h G w v) := (hH.eq w v).symm
  rw [eichlerMatrix_mulVec, eichlerMatrix_mulVec]
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hww, hwy, hyw, hvy, hvw, map_mul]
  linear_combination (h.bar (gramForm h G w v) * gramForm h G w v') * hc

theorem eichlerMatrix_sub_one_pow_three (hH : (gramForm h G).IsSymm) {w y : Fin n → K}
    (hww : gramForm h G w w = 0) (hwy : gramForm h G w y = 0) (c : K) :
    (eichlerMatrix h G w y c - 1) ^ 3 = 0 := by
  have hyw : gramForm h G y w = 0 := by rw [← hH.eq w y, hwy, map_zero]
  refine sub_one_pow_three_eq_zero fun v => ?_
  simp only [eichlerMatrix_mulVec, map_add, map_sub, map_smul, smul_eq_mul, hww, hwy, hyw]
  simp only [mul_zero, zero_smul, sub_zero, add_zero, zero_mul, sub_self]

theorem eichlerGL_mem (hH : (gramForm h G).IsSymm) {w y : Fin n → K}
    (hww : gramForm h G w w = 0) (hwy : gramForm h G w y = 0) {c : K}
    (hc : c + h.bar c = -gramForm h G y y) :
    unipotentGL (eichlerMatrix h G w y c) (eichlerMatrix_sub_one_pow_three hH hww hwy c) ∈
      gramSU h G :=
  mem_gramSU_iff_isometry.mpr ⟨fun v v' => eichlerMatrix_isometry hH hww hwy hc v v',
    det_eq_one_of_sub_one_pow_three (eichlerMatrix_sub_one_pow_three hH hww hwy c)⟩

end Eichler

section Radical

variable (h : UnitaryFieldData p f K) (G : Matrix (Fin n) (Fin n) K)

@[expose] def IsRadicalMatrix (W : Submodule K (Fin n → K)) (M : Matrix (Fin n) (Fin n) K) :
    Prop :=
  (∀ w ∈ W, M *ᵥ w = w) ∧ (∀ v ∈ W.orthogonalBilin (gramForm h G), M *ᵥ v - v ∈ W) ∧
    ∀ v, M *ᵥ v - v ∈ W.orthogonalBilin (gramForm h G)

variable {h G}

theorem isRadicalMatrix_one (W : Submodule K (Fin n → K)) : IsRadicalMatrix h G W 1 :=
  ⟨fun w _ => one_mulVec w, fun v _ => by rw [one_mulVec, sub_self]; exact zero_mem _,
    fun v => by rw [one_mulVec, sub_self]; exact zero_mem _⟩

theorem IsRadicalMatrix.mul {W : Submodule K (Fin n → K)} {M M' : Matrix (Fin n) (Fin n) K}
    (hM : IsRadicalMatrix h G W M) (hM' : IsRadicalMatrix h G W M') :
    IsRadicalMatrix h G W (M * M') := by
  obtain ⟨h1, h2, h3⟩ := hM
  obtain ⟨h1', h2', h3'⟩ := hM'
  refine ⟨fun w hw => by rw [← mulVec_mulVec, h1' w hw, h1 w hw], fun v hv => ?_, fun v => ?_⟩
  · have hv' : M' *ᵥ v ∈ W.orthogonalBilin (gramForm h G) := by
      have := add_mem (h3' v) hv
      rwa [sub_add_cancel] at this
    have := add_mem (h2 _ hv') (h2' v hv)
    rwa [sub_add_sub_cancel, mulVec_mulVec] at this
  · have := add_mem (h3 (M' *ᵥ v)) (h3' v)
    rwa [sub_add_sub_cancel, mulVec_mulVec] at this

theorem IsRadicalMatrix.of_mul_eq_one {W : Submodule K (Fin n → K)}
    {M M' : Matrix (Fin n) (Fin n) K} (hM : IsRadicalMatrix h G W M) (hMM : M * M' = 1)
    (hMM' : M' * M = 1) : IsRadicalMatrix h G W M' := by
  obtain ⟨h1, h2, h3⟩ := hM
  have hgg : ∀ v, M *ᵥ (M' *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMM, one_mulVec]
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · conv_lhs => rw [← h1 w hw]
    rw [mulVec_mulVec, hMM', one_mulVec]
  · have hu : M' *ᵥ v ∈ W.orthogonalBilin (gramForm h G) := by
      have := sub_mem hv (h3 (M' *ᵥ v))
      rwa [hgg, sub_sub_cancel] at this
    have := neg_mem (h2 _ hu)
    rwa [hgg, neg_sub] at this
  · have := neg_mem (h3 (M' *ᵥ v))
    rwa [hgg, neg_sub] at this

variable (h G)

@[expose] def isotropicRadical (W : Submodule K (Fin n → K)) : Subgroup (gramSU h G) where
  carrier := {g | IsRadicalMatrix h G W ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  one_mem' := isRadicalMatrix_one W
  mul_mem' hg hg' := IsRadicalMatrix.mul hg hg'
  inv_mem' {g} hg := IsRadicalMatrix.of_mul_eq_one hg (g : GL (Fin n) K).val_inv
    (g : GL (Fin n) K).inv_val

variable {h G} in
theorem mem_isotropicRadical {W : Submodule K (Fin n → K)} {g : gramSU h G} :
    g ∈ isotropicRadical h G W ↔
      (∀ w ∈ W, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
      (∀ v ∈ W.orthogonalBilin (gramForm h G),
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W) ∧
      ∀ v, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈
        W.orthogonalBilin (gramForm h G) :=
  Iff.rfl

variable {h G} in
theorem sub_one_pow_three_of_mem_radical {W : Submodule K (Fin n → K)} {g : gramSU h G}
    (hg : g ∈ isotropicRadical h G W) :
    (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) ^ 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := mem_isotropicRadical.mp hg
  refine sub_one_pow_three_eq_zero fun v => ?_
  rw [h1 _ (h2 _ (h3 v)), sub_self]

variable {h G} in
theorem pow_four_eq_one_of_mem_radical [CharP K 2] {W : Submodule K (Fin n → K)}
    {g : gramSU h G} (hg : g ∈ isotropicRadical h G W) : g ^ 4 = 1 :=
  Subtype.ext (Units.ext (by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    exact pow_four_eq_one_of_sub_one_pow_three (sub_one_pow_three_of_mem_radical hg)))

variable {h G} in
theorem eichler_mem_radical (hH : (gramForm h G).IsSymm) {W : Submodule K (Fin n → K)}
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h G v w = 0) {w y : Fin n → K} (hw : w ∈ W)
    (hy : y ∈ W.orthogonalBilin (gramForm h G)) {c : K} (hc : c + h.bar c = -gramForm h G y y) :
    (⟨_, eichlerGL_mem hH (hWiso w hw w hw) (Submodule.mem_orthogonalBilin.mp hy w hw) hc⟩ :
      gramSU h G) ∈ isotropicRadical h G W := by
  have hWL : ∀ v ∈ W, v ∈ W.orthogonalBilin (gramForm h G) := fun v hv =>
    Submodule.mem_orthogonalBilin.mpr fun u hu => hWiso u hu v hv
  have hyv : ∀ v ∈ W, gramForm h G y v = 0 := fun v hv => by
    rw [← hH.eq v y, Submodule.mem_orthogonalBilin.mp hy v hv, map_zero]
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v => ?_⟩
  · change eichlerMatrix h G w y c *ᵥ v = v
    rw [eichlerMatrix_mulVec, hWiso w hw v hv, hyv v hv]
    simp
  · change eichlerMatrix h G w y c *ᵥ v - v ∈ W
    have key : eichlerMatrix h G w y c *ᵥ v - v = -(gramForm h G y v • w) := by
      rw [eichlerMatrix_mulVec, Submodule.mem_orthogonalBilin.mp hv w hw, zero_smul, add_zero,
        mul_zero, zero_smul, add_zero]
      abel
    rw [key]
    exact neg_mem (Submodule.smul_mem _ _ hw)
  · change eichlerMatrix h G w y c *ᵥ v - v ∈ W.orthogonalBilin (gramForm h G)
    have key : eichlerMatrix h G w y c *ᵥ v - v = gramForm h G w v • y - gramForm h G y v • w +
        (c * gramForm h G w v) • w := by
      rw [eichlerMatrix_mulVec]
      abel
    rw [key]
    exact add_mem (sub_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ (hWL w hw)))
      (Submodule.smul_mem _ _ (hWL w hw))

@[expose] noncomputable def gramSUToUnitary : gramSU h G →* primeFormUnitary h G :=
  Subgroup.inclusion fun _ hg => hg.1

@[expose] noncomputable def radicalConjHom (W : Submodule K (Fin n → K)) :
    isotropicRadical h G W →* MulAut (primeFormP h G) :=
  (primeFormConjHom h G).comp ((gramSUToUnitary h G).comp (isotropicRadical h G W).subtype)

theorem radicalConjHom_apply (W : Submodule K (Fin n → K)) (g : isotropicRadical h G W) :
    radicalConjHom h G W g = primeFormConjHom h G (gramSUToUnitary h G g) :=
  rfl

@[expose] noncomputable def radicalImage (W : Submodule K (Fin n → K)) :
    Subgroup (MulAut (primeFormP h G)) :=
  (radicalConjHom h G W).range

end Radical

section Psi

variable (h : UnitaryFieldData p f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

theorem primeFormConjHom_eq_psi (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A = primeFormPsi h hC ⟨A, 1⟩ := by
  rw [primeFormPsi_apply, map_one, mul_one]

include hC in
theorem eq_scalar_of_primeFormConjHom_eq_one (hn : 3 ≤ n)
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)} (hA : primeFormConjHom h _ A = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  rw [primeFormConjHom_eq_psi h hC] at hA
  obtain ⟨-, c, hc, hAc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hA
  exact ⟨c, hc, hAc⟩

include hC in
theorem radicalConjHom_injective (hn : 3 ≤ n) {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥) :
    Function.Injective (radicalConjHom h (C : Matrix (Fin n) (Fin n) K) W) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, -, hgc⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hn hg
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have h1 := (mem_isotropicRadical.mp g.2).1 w hw
  have hg1 : ((g : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hgc
  have hc : c = 1 := by
    rw [hg1, GeneralLinearGroup.coe_scalar, scalar_apply] at h1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
    have h3 := congrFun h1 i
    rw [mulVec_diagonal] at h3
    exact Units.ext (mul_right_cancel₀ hi (h3.trans (one_mul _).symm))
  refine Subtype.ext (Subtype.ext ?_)
  rw [hg1, hc, map_one]
  rfl

theorem psi_mul_conj_mul_inv (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K) (g : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormPsi h hC ⟨A, φ⟩ * primeFormConjHom h _ g * (primeFormPsi h hC ⟨A, φ⟩)⁻¹ =
      primeFormConjHom h _ (A * primeFormFieldU h hC φ g * A⁻¹) := by
  rw [primeFormPsi_apply, map_mul, map_mul, map_inv, ← primeFormField_conj_eq h hC φ g]
  group

end Psi

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
