module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedSymplectic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open Matrix CFSG.Assembly.LowTwoRank

variable (r : ℕ) (K : Type) [Field K]

@[expose] def isoFlag (i : ℕ) : Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K
    ((fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) '' {j | (j : ℕ) < i})

@[expose] def flag (i : ℕ) : Submodule K (Fin r ⊕ Fin r → K) :=
  if i ≤ r then isoFlag r K i else (pairedSympForm K r).orthogonal (isoFlag r K (2 * r - i))

variable {r K}

theorem mem_isoFlag {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ isoFlag r K i ↔
      (∀ j, v (Sum.inr j) = 0) ∧ ∀ j : Fin r, i ≤ (j : ℕ) → v (Sum.inl j) = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨fun j => by simp, fun j hj => ?_⟩
      have hkj : k ≠ j := fun h => by
        subst h
        exact absurd hk (not_lt.mpr hj)
      simp [hkj.symm]
    | zero => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun j => by simp [hx.1 j, hy.1 j], fun j hj => by simp [hx.2 j hj, hy.2 j hj]⟩
    | smul c x _ hx => exact ⟨fun j => by simp [hx.1 j], fun j hj => by simp [hx.2 j hj]⟩
  · rintro ⟨h1, h2⟩
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun x _ => ?_
    rcases x with j | j
    · by_cases hj : (j : ℕ) < i
      · have : (Pi.single (Sum.inl j) (v (Sum.inl j)) : Fin r ⊕ Fin r → K) =
            v (Sum.inl j) • Pi.single (Sum.inl j) 1 := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · rw [h2 j (not_lt.mp hj), Pi.single_zero]
        exact Submodule.zero_mem _
    · rw [h1 j, Pi.single_zero]
      exact Submodule.zero_mem _

theorem pairedSympForm_single_inl (j : Fin r) (v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (Pi.single (Sum.inl j) 1) v = v (Sum.inr j) := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem mem_orthogonal_isoFlag {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ (pairedSympForm K r).orthogonal (isoFlag r K i) ↔
      ∀ j : Fin r, (j : ℕ) < i → v (Sum.inr j) = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h j hj
    rw [← pairedSympForm_single_inl j v]
    exact h _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · intro h n hn
    obtain ⟨hn1, hn2⟩ := mem_isoFlag.mp hn
    rw [pairedSympForm_apply]
    have hr : (n ∘ Sum.inr : Fin r → K) = 0 := funext fun j => hn1 j
    rw [hr, zero_dotProduct, sub_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < i
    · simp [h j hj]
    · simp [hn2 j (not_lt.mp hj)]

theorem mem_flag_of_le {i : ℕ} (hi : i ≤ r) {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K i ↔ v ∈ isoFlag r K i := by
  rw [flag, ite_eq_left hi]

theorem mem_flag_of_lt {i : ℕ} (hi : r < i) {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K i ↔ ∀ j : Fin r, (j : ℕ) < 2 * r - i → v (Sum.inr j) = 0 := by
  rw [flag, ite_eq_right (not_le.mpr hi), mem_orthogonal_isoFlag]

variable (r K) in
@[expose] def stabilizer (W : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (StatedSp r K) where
  carrier := {g | W.map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W}
  one_mem' := by
    change W.map (mulVecLin (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W
    rw [mulVecLin_one, Submodule.map_id]
  mul_mem' := fun {g h} hg hh => by
    change W.map (mulVecLin (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      * ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) = W
    rw [mulVecLin_mul, Submodule.map_comp, hh, hg]
  inv_mem' := fun {g} hg => by
    have hg' : W.map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W := hg
    change W.map (mulVecLin (((g : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W
    conv_lhs => rw [← hg']
    rw [← Submodule.map_comp, ← mulVecLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulVecLin_one, Submodule.map_id]

theorem mem_stabilizer {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K} :
    g ∈ stabilizer r K W ↔ W.map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W :=
  Iff.rfl

theorem mem_stabilizer_of_mulVec_mem {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (h₁ : ∀ v ∈ W, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W)
    (h₂ : ∀ v ∈ W, (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) :
    g ∈ stabilizer r K W := by
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun v hv => ⟨_, h₂ v hv, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact h₁ v hv
  · rw [mulVecLin_apply, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, one_mulVec]

variable (r K)

@[expose] def borelSubgroup : Subgroup (StatedSp r K) :=
  ⨅ i ∈ Set.Icc 1 r, stabilizer r K (flag r K i)

variable {r K}

theorem mem_borelSubgroup {g : StatedSp r K} :
    g ∈ borelSubgroup r K ↔ ∀ i, 1 ≤ i → i ≤ r → g ∈ stabilizer r K (flag r K i) := by
  simp only [borelSubgroup, Subgroup.mem_iInf, Set.mem_Icc, and_imp]

theorem mem_borelSubgroup_iff_isoFlag {g : StatedSp r K} :
    g ∈ borelSubgroup r K ↔ ∀ i, 1 ≤ i → i ≤ r → g ∈ stabilizer r K (isoFlag r K i) := by
  rw [mem_borelSubgroup]
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => ?_
  rw [show flag r K i = isoFlag r K i from by rw [flag, ite_eq_left hi]]

@[expose] def IsUnitriangular (A : Matrix (Fin r) (Fin r) K) : Prop :=
  A.IsUpperTriangular ∧ ∀ i, A i i = 1

theorem mul_apply_self_of_isUpperTriangular {A D : Matrix (Fin r) (Fin r) K}
    (hA : A.IsUpperTriangular) (hD : D.IsUpperTriangular) (i : Fin r) :
    (A * D) i i = A i i * D i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hA h, zero_mul]
    · rw [hD h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem isUnitriangular_one : IsUnitriangular (1 : Matrix (Fin r) (Fin r) K) :=
  ⟨blockTriangular_one, fun _ => one_apply_eq _⟩

theorem IsUnitriangular.det_eq_one {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A) :
    A.det = 1 := by
  rw [det_of_isUpperTriangular hA.1]
  exact Finset.prod_eq_one fun i _ => hA.2 i

theorem IsUnitriangular.isUnit_det {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A) :
    IsUnit A.det := by
  rw [hA.det_eq_one]
  exact isUnit_one

theorem IsUnitriangular.mul {A D : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A)
    (hD : IsUnitriangular D) : IsUnitriangular (A * D) :=
  ⟨hA.1.mul hD.1, fun i => by rw [mul_apply_self_of_isUpperTriangular hA.1 hD.1, hA.2, hD.2,
    one_mul]⟩

theorem isUpperTriangular_inv {A : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) : A⁻¹.IsUpperTriangular := by
  have := invertibleOfIsUnitDet A hdet
  exact blockTriangular_inv_of_blockTriangular hA

theorem mul_inv_apply_self_of_isUpperTriangular {A : Matrix (Fin r) (Fin r) K}
    (hA : A.IsUpperTriangular) (hdet : IsUnit A.det) (i : Fin r) : A i i * A⁻¹ i i = 1 := by
  rw [← mul_apply_self_of_isUpperTriangular hA (isUpperTriangular_inv hA hdet),
    mul_nonsing_inv A hdet, one_apply_eq]

theorem IsUnitriangular.inv {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A) :
    IsUnitriangular A⁻¹ :=
  ⟨isUpperTriangular_inv hA.1 hA.isUnit_det, fun i => by
    have h := mul_inv_apply_self_of_isUpperTriangular hA.1 hA.isUnit_det i
    rwa [hA.2, one_mul] at h⟩

@[expose] def blockMat (A C : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks A (A * C) 0 A⁻¹ᵀ

theorem blockMat_one : blockMat (1 : Matrix (Fin r) (Fin r) K) 0 = 1 := by
  simp [blockMat, fromBlocks_one]

theorem blockMat_mul {A C D E : Matrix (Fin r) (Fin r) K} (hD : IsUnit D.det) :
    blockMat A C * blockMat D E = blockMat (A * D) (E + D⁻¹ * C * D⁻¹ᵀ) := by
  rw [blockMat, blockMat, blockMat, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_assoc A D E, Matrix.mul_assoc A D, Matrix.mul_assoc D⁻¹ C,
      mul_nonsing_inv_cancel_left D _ hD, Matrix.mul_assoc A C]
  · rw [Matrix.zero_mul, zero_add, Matrix.mul_inv_rev, transpose_mul]

theorem blockMat_mul_inv {A C : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    blockMat A C * blockMat A⁻¹ (-(A * C * Aᵀ)) = 1 := by
  rw [blockMat_mul (isUnit_nonsing_inv_det A hA), mul_nonsing_inv A hA,
    nonsing_inv_nonsing_inv A hA, neg_add_cancel, blockMat_one]

theorem blockMat_eq_mul (A C : Matrix (Fin r) (Fin r) K) :
    blockMat A C = fromBlocks A 0 0 A⁻¹ᵀ * fromBlocks 1 C 0 1 := by
  simp [blockMat, fromBlocks_multiply]

variable (r K) in
@[expose] def upperUnipotentSp {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) : StatedSp r K :=
  ⟨(CFSG.ClassicalGroups.Symplectic.upperUnipotent hC : GL (Fin r ⊕ Fin r) K), by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (CFSG.ClassicalGroups.Symplectic.upperUnipotent hC).2⟩

@[simp]
theorem coe_upperUnipotentSp {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) :
    (((upperUnipotentSp r K hC : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = fromBlocks 1 C 0 1 :=
  CFSG.ClassicalGroups.Symplectic.coe_upperUnipotent hC

@[expose] def blockElt {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) : StatedSp r K :=
  SymplecticTorusWeyl.leviSp (nonsingInvUnit A hA) * upperUnipotentSp r K hC

theorem coe_blockElt {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) :
    (((blockElt hA hC : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C := by
  rw [blockElt, Subgroup.coe_mul, Units.val_mul, SymplecticTorusWeyl.coe_leviSp,
    coe_upperUnipotentSp, blockMat_eq_mul]
  rfl

theorem blockMat_mem_statedSp {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) :
    ∃ g : StatedSp r K, ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C :=
  ⟨blockElt hA hC, coe_blockElt hA hC⟩

variable (r K)

@[expose] def unipotent : Subgroup (StatedSp r K) where
  carrier := {g | ∃ A C : Matrix (Fin r) (Fin r) K, IsUnitriangular A ∧ Cᵀ = C ∧
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C}
  one_mem' := ⟨1, 0, isUnitriangular_one, transpose_zero, by
    rw [blockMat_one]
    rfl⟩
  mul_mem' := by
    rintro g h ⟨A, C, hA, hC, hg⟩ ⟨D, E, hD, hE, hh⟩
    refine ⟨A * D, E + D⁻¹ * C * D⁻¹ᵀ, hA.mul hD, ?_, ?_⟩
    · rw [transpose_add, hE, transpose_mul, transpose_mul, transpose_transpose, hC,
        Matrix.mul_assoc]
    · rw [Subgroup.coe_mul, Units.val_mul, hg, hh, blockMat_mul hD.isUnit_det]
  inv_mem' := by
    rintro g ⟨A, C, hA, hC, hg⟩
    refine ⟨A⁻¹, -(A * C * Aᵀ), hA.inv, ?_, ?_⟩
    · rw [transpose_neg, transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]
    · have h₁ : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          blockMat A⁻¹ (-(A * C * Aᵀ)) = 1 := by
        rw [hg, blockMat_mul_inv hA.isUnit_det]
      exact Units.inv_eq_of_mul_eq_one_right h₁

variable {r K}

theorem mem_unipotent {g : StatedSp r K} :
    g ∈ unipotent r K ↔ ∃ A C : Matrix (Fin r) (Fin r) K, IsUnitriangular A ∧ Cᵀ = C ∧
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C :=
  Iff.rfl

theorem exists_mem_unipotent {A C : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A)
    (hC : Cᵀ = C) :
    ∃ g ∈ unipotent r K, ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A C :=
  ⟨blockElt hA.isUnit_det hC, ⟨A, C, hA, hC, coe_blockElt hA.isUnit_det hC⟩,
    coe_blockElt hA.isUnit_det hC⟩

theorem blockMat_mulVec_mem_isoFlag {A : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (C : Matrix (Fin r) (Fin r) K) {i : ℕ} {v : Fin r ⊕ Fin r → K} (hv : v ∈ isoFlag r K i) :
    blockMat A C *ᵥ v ∈ isoFlag r K i := by
  obtain ⟨hv1, hv2⟩ := mem_isoFlag.mp hv
  have hr : (v ∘ Sum.inr : Fin r → K) = 0 := funext fun j => hv1 j
  rw [mem_isoFlag]
  simp only [blockMat, fromBlocks_mulVec, hr, mulVec_zero, add_zero, zero_mulVec, Sum.elim_inr,
    Sum.elim_inl, Pi.zero_apply, implies_true, true_and]
  intro j hj
  change ∑ k, A j k * v (Sum.inl k) = 0
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hkj : k < j
  · rw [hA hkj, zero_mul]
  · rw [hv2 k (hj.trans (Fin.le_def.mp (not_lt.mp hkj))), mul_zero]

theorem mem_borelSubgroup_of_coe_eq_blockMat {g : StatedSp r K} {A C : Matrix (Fin r) (Fin r) K}
    (hA : A.IsUpperTriangular) (hdet : IsUnit A.det)
    (hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      blockMat A C) : g ∈ borelSubgroup r K := by
  rw [mem_borelSubgroup_iff_isoFlag]
  intro i _ _
  have hinv : (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockMat A⁻¹ (-(A * C * Aᵀ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg, blockMat_mul_inv hdet]
  refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) fun v hv => ?_
  · rw [hg]
    exact blockMat_mulVec_mem_isoFlag hA C hv
  · rw [hinv]
    exact blockMat_mulVec_mem_isoFlag (isUpperTriangular_inv hA hdet) _ hv

theorem unipotent_le_borelSubgroup : unipotent r K ≤ borelSubgroup r K := by
  rintro g ⟨A, C, hA, -, hg⟩
  exact mem_borelSubgroup_of_coe_eq_blockMat hA.1 hA.isUnit_det hg

theorem diagonal_mulVec_mem_isoFlag (d : Fin r ⊕ Fin r → K) {i : ℕ} {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ isoFlag r K i) : diagonal d *ᵥ v ∈ isoFlag r K i := by
  obtain ⟨hv1, hv2⟩ := mem_isoFlag.mp hv
  rw [mem_isoFlag]
  simp only [mulVec_diagonal]
  exact ⟨fun j => by rw [hv1 j, mul_zero], fun j hj => by rw [hv2 j hj, mul_zero]⟩

theorem torus_le_borelSubgroup : SymplecticTorusWeyl.torus r K ≤ borelSubgroup r K := by
  rintro _ ⟨t, rfl⟩
  rw [mem_borelSubgroup_iff_isoFlag]
  intro i _ _
  refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) fun v hv => ?_
  · rw [SymplecticTorusWeyl.coe_torusHom]
    exact diagonal_mulVec_mem_isoFlag _ hv
  · rw [← map_inv, SymplecticTorusWeyl.coe_torusHom]
    exact diagonal_mulVec_mem_isoFlag _ hv

variable (r K)

@[expose] def proj : StatedSp r K →* StatedProj (StatedSp r K) :=
  QuotientGroup.mk' _

@[expose] def projBorel : Subgroup (StatedProj (StatedSp r K)) :=
  (borelSubgroup r K).map (proj r K)

@[expose] def projUnipotent : Subgroup (StatedProj (StatedSp r K)) :=
  (unipotent r K).map (proj r K)

section Weyl

open CFSG.LieType.Universal.SpecialLinear

variable {r K}

@[expose] def dotSign (w : Equiv.Perm (Fin r ⊕ Fin r)) : Fin r ⊕ Fin r → K :=
  Sum.elim (fun _ => 1) fun i => Sum.elim (fun _ => -1) (fun _ => 1) (w (Sum.inr i))

theorem dotSign_mul_self (w : Equiv.Perm (Fin r ⊕ Fin r)) (x : Fin r ⊕ Fin r) :
    dotSign (K := K) w x * dotSign w x = 1 := by
  rcases x with i | i
  · simp [dotSign]
  · simp only [dotSign, Sum.elim_inr]
    rcases w (Sum.inr i) with j | j <;> simp

theorem transpose_signedPerm {ι : Type*} [DecidableEq ι] (π : Equiv.Perm ι) (ε : ι → K) :
    (signedPerm π ε)ᵀ = signedPerm π⁻¹ fun s => ε (π⁻¹ s) := by
  ext a b
  rw [transpose_apply, signedPerm_apply, signedPerm_apply]
  by_cases h : b = π a
  · subst h
    simp
  · have h' : a ≠ π⁻¹ b := fun h' => h (by
      rw [h', ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply])
    rw [ite_eq_right h, ite_eq_right h']

theorem blueprintJ_eq_signedPerm :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      signedPerm (Equiv.sumComm (Fin r) (Fin r)) (Sum.elim (fun _ => -1) fun _ => 1) := by
  ext (a | a) (b | b) <;> by_cases h : a = b <;> simp [signedPerm_apply, one_apply, h, eq_comm]

theorem signedPerm_dotSign_symplectic {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ SymplecticTorusWeyl.signedPermGroup r) :
    (signedPerm w (dotSign (K := K) w))ᵀ * fromBlocks 0 1 (-1) 0 * signedPerm w (dotSign w) =
      fromBlocks 0 1 (-1) 0 := by
  have hsw : ∀ s, w⁻¹ (Equiv.sumComm (Fin r) (Fin r) (w s)) = s.swap := fun s => by
    rw [Equiv.sumComm_apply, ← SymplecticTorusWeyl.mem_signedPermGroup.mp hw s,
      ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [blueprintJ_eq_signedPerm, transpose_signedPerm, signedPerm_mul_signedPerm,
    signedPerm_mul_signedPerm]
  have hperm : w⁻¹ * Equiv.sumComm (Fin r) (Fin r) * w = Equiv.sumComm (Fin r) (Fin r) :=
    Equiv.ext fun s => by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsw,
      Equiv.sumComm_apply]
  rw [hperm]
  congr 1
  funext s
  simp only [hsw]
  rcases s with i | i
  · have h := SymplecticTorusWeyl.mem_signedPermGroup.mp hw (Sum.inl i)
    simp only [Sum.swap_inl] at h
    simp only [Sum.swap_inl, dotSign, Sum.elim_inl, Sum.elim_inr, mul_one, h]
    rcases w (Sum.inl i) with j | j <;> simp
  · have h := SymplecticTorusWeyl.mem_signedPermGroup.mp hw (Sum.inl i)
    simp only [Sum.swap_inl] at h
    simp only [Sum.swap_inr, dotSign, Sum.elim_inl, Sum.elim_inr, one_mul, h]
    rcases w (Sum.inl i) with j | j <;> simp

theorem signedPerm_mul_transpose_self (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    signedPerm w (dotSign (K := K) w) * (signedPerm w (dotSign w))ᵀ = 1 := by
  rw [transpose_signedPerm, signedPerm_mul_signedPerm, mul_inv_cancel, signedPerm_one,
    ← diagonal_one]
  congr 1
  funext s
  exact dotSign_mul_self w _

theorem transpose_mul_signedPerm_self (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    (signedPerm w (dotSign (K := K) w))ᵀ * signedPerm w (dotSign w) = 1 := by
  rw [transpose_signedPerm, signedPerm_mul_signedPerm, inv_mul_cancel, signedPerm_one,
    ← diagonal_one]
  congr 1
  funext s
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  exact dotSign_mul_self w _

variable (K) in
@[expose] def dotW (w : SymplecticTorusWeyl.signedPermGroup r) : StatedSp r K :=
  ⟨⟨signedPerm w (dotSign w), (signedPerm w (dotSign w))ᵀ, signedPerm_mul_transpose_self _,
    transpose_mul_signedPerm_self _⟩,
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (signedPerm_dotSign_symplectic w.2)⟩

theorem coe_dotW (w : SymplecticTorusWeyl.signedPermGroup r) :
    (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = signedPerm w (dotSign w) :=
  rfl

theorem dotW_mulVec_single (w : SymplecticTorusWeyl.signedPermGroup r) (x : Fin r ⊕ Fin r) :
    (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single x 1 =
      dotSign (K := K) w x • Pi.single ((w : Equiv.Perm (Fin r ⊕ Fin r)) x) 1 := by
  rw [coe_dotW, mulVec_single_one]
  funext y
  simp only [col_apply, signedPerm_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

theorem dotW_mulVec_inl (w : SymplecticTorusWeyl.signedPermGroup r) {i j : Fin r}
    (h : (w : Equiv.Perm (Fin r ⊕ Fin r)) (Sum.inl i) = Sum.inl j) :
    (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single (Sum.inl i) 1 =
        Pi.single (Sum.inl j) 1 ∧
      (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single (Sum.inr i) 1 =
        Pi.single (Sum.inr j) 1 := by
  have h' : (w : Equiv.Perm (Fin r ⊕ Fin r)) (Sum.inr i) = Sum.inr j := by
    have := SymplecticTorusWeyl.mem_signedPermGroup.mp w.2 (Sum.inl i)
    rwa [Sum.swap_inl, h, Sum.swap_inl] at this
  rw [dotW_mulVec_single, dotW_mulVec_single, h, h']
  simp [dotSign, h']

theorem dotW_mulVec_inr (w : SymplecticTorusWeyl.signedPermGroup r) {i j : Fin r}
    (h : (w : Equiv.Perm (Fin r ⊕ Fin r)) (Sum.inl i) = Sum.inr j) :
    (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single (Sum.inl i) 1 =
        Pi.single (Sum.inr j) 1 ∧
      (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ Pi.single (Sum.inr i) 1 =
        -Pi.single (Sum.inl j) 1 := by
  have h' : (w : Equiv.Perm (Fin r ⊕ Fin r)) (Sum.inr i) = Sum.inl j := by
    have := SymplecticTorusWeyl.mem_signedPermGroup.mp w.2 (Sum.inl i)
    rwa [Sum.swap_inl, h, Sum.swap_inr] at this
  rw [dotW_mulVec_single, dotW_mulVec_single, h, h']
  simp [dotSign, h']

end Weyl

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
