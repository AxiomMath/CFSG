module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.GroupBinaryPolar
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.LieType.Universal.Spin

variable {r : ℕ} {K : Type*} [Field K]

variable (r K) in
@[expose] noncomputable def matrixEquiv :
    GL (Fin r ⊕ Fin r) K ≃* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin r ⊕ Fin r → K))

theorem matrixEquiv_apply (M : GL (Fin r ⊕ Fin r) K) (v : Fin r ⊕ Fin r → K) :
    matrixEquiv r K M v = (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v :=
  rfl

theorem toMatrix'_matrixEquiv (M : GL (Fin r ⊕ Fin r) K) :
    LinearMap.toMatrix' ((matrixEquiv r K M : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = M :=
  LinearMap.toMatrix'_toLin' _

@[expose] noncomputable def leviGL : GL (Fin r) K →* GL (Fin r ⊕ Fin r) K where
  toFun A := ⟨blockDiagInv (A : Matrix (Fin r) (Fin r) K),
    blockDiagInv ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K), by
      rw [← blockDiagInv_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockDiagInv_one],
    by
      rw [← blockDiagInv_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockDiagInv_one]⟩
  map_one' := Units.ext (by
    change blockDiagInv ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1
    rw [Units.val_one, blockDiagInv_one])
  map_mul' A B := Units.ext (by
    change blockDiagInv ((A * B : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      blockDiagInv (A : Matrix (Fin r) (Fin r) K) * blockDiagInv (B : Matrix (Fin r) (Fin r) K)
    rw [Units.val_mul, blockDiagInv_mul])

theorem coe_leviGL (A : GL (Fin r) K) :
    (leviGL A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      blockDiagInv (A : Matrix (Fin r) (Fin r) K) :=
  rfl

variable (r K) in
@[expose] noncomputable def levi :
    GL (Fin r) K →* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (matrixEquiv r K).toMonoidHom.comp leviGL

theorem levi_eq_matrixEquiv (A : GL (Fin r) K) : levi r K A = matrixEquiv r K (leviGL A) :=
  rfl

theorem toMatrix'_levi (A : GL (Fin r) K) :
    LinearMap.toMatrix' ((levi r K A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        blockDiagInv (A : Matrix (Fin r) (Fin r) K) :=
  toMatrix'_matrixEquiv _

theorem toMatrix'_levi_eq (A : GL (Fin r) K) :
    LinearMap.toMatrix' ((levi r K A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * 0) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [toMatrix'_levi, blockDiagInv, Matrix.mul_zero, Matrix.coe_units_inv]

theorem levi_mem_maxStab (A : GL (Fin r) K) : levi r K A ∈ maxStab r K :=
  mem_maxStab_of_toMatrix' A 0 (by rw [transpose_zero, neg_zero]) (fun _ => rfl)
    (toMatrix'_levi_eq A)

theorem levi_mem_orthogonalGroup (A : GL (Fin r) K) :
    levi r K A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
  (mem_maxStab.1 (levi_mem_maxStab A)).1

theorem levi_injective : Function.Injective (levi r K) := by
  intro A B h
  have h' := congrArg (fun g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
    LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) h
  simp only [toMatrix'_levi, blockDiagInv] at h'
  exact Units.ext (Matrix.fromBlocks_inj.1 h').1

theorem levi_mem_posUnip {A : GL (Fin r) K}
    (hA : (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) : levi r K A ∈ posUnip r K :=
  mem_posUnip_iff.2 ⟨A, 0, hA, h1, by rw [transpose_zero, neg_zero], fun _ => rfl,
    toMatrix'_levi_eq A⟩

theorem levi_toGL_mem_orthElementaryGroup [CharP K 2] (hr : 3 ≤ r)
    (A : SpecialLinearGroup (Fin r) K) :
    levi r K (SpecialLinearGroup.toGL A) ∈ orthElementaryGroup (quadPlus r K) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hr
  set R := ((levi r K).comp SpecialLinearGroup.toGL).range with hR
  have : Group.IsPerfect R := Group.IsPerfect.range _
  have hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
    rintro _ ⟨B, rfl⟩
    exact levi_mem_orthogonalGroup _
  have hmem : levi r K (SpecialLinearGroup.toGL A) ∈ R := ⟨A, rfl⟩
  rw [← Subgroup.commutator_eq_self (H := R)] at hmem
  rw [← commutator_orthogonalGroup_quadPlus hr]
  exact Subgroup.commutator_mono hRO hRO hmem

variable (r K) in
@[expose] def altSubgroup : AddSubgroup (Matrix (Fin r) (Fin r) K) where
  carrier := {B | Bᵀ = -B ∧ ∀ i, B i i = 0}
  add_mem' {B C} hB hC := ⟨by rw [transpose_add, hB.1, hC.1, neg_add], fun i => by
    rw [Matrix.add_apply, hB.2 i, hC.2 i, add_zero]⟩
  zero_mem' := ⟨by rw [transpose_zero, neg_zero], fun _ => rfl⟩
  neg_mem' {B} hB := ⟨by rw [transpose_neg, hB.1], fun i => by
    rw [Matrix.neg_apply, hB.2 i, neg_zero]⟩

theorem mem_altSubgroup {B : Matrix (Fin r) (Fin r) K} :
    B ∈ altSubgroup r K ↔ Bᵀ = -B ∧ ∀ i, B i i = 0 :=
  Iff.rfl

theorem congr_mem_altSubgroup (A : Matrix (Fin r) (Fin r) K) {B : Matrix (Fin r) (Fin r) K}
    (hB : B ∈ altSubgroup r K) : A * B * Aᵀ ∈ altSubgroup r K := by
  refine alternating_of_mulVec_dotProduct_self fun y => ?_
  calc (A * B * Aᵀ) *ᵥ y ⬝ᵥ y = (B *ᵥ (Aᵀ *ᵥ y)) ⬝ᵥ (Aᵀ *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm,
          Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    _ = 0 := mulVec_dotProduct_self_eq_zero hB.1 hB.2 _

@[expose] noncomputable def radicalGL :
    Multiplicative (Matrix (Fin r) (Fin r) K) →* GL (Fin r ⊕ Fin r) K where
  toFun B := ⟨blockUnip B.toAdd, blockUnip (-B.toAdd), by
      rw [← blockUnip_add, add_neg_cancel, blockUnip_zero], by
      rw [← blockUnip_add, neg_add_cancel, blockUnip_zero]⟩
  map_one' := Units.ext (by
    change blockUnip (Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin r) (Fin r) K))) = 1
    rw [toAdd_one, blockUnip_zero])
  map_mul' B C := Units.ext (by
    change blockUnip (Multiplicative.toAdd (B * C)) = blockUnip B.toAdd * blockUnip C.toAdd
    rw [toAdd_mul, blockUnip_add])

theorem coe_radicalGL (B : Multiplicative (Matrix (Fin r) (Fin r) K)) :
    (radicalGL B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = blockUnip B.toAdd :=
  rfl

variable (r K) in
@[expose] noncomputable def radical :
    Multiplicative (Matrix (Fin r) (Fin r) K) →*
      ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (matrixEquiv r K).toMonoidHom.comp radicalGL

theorem radical_eq_matrixEquiv (B : Multiplicative (Matrix (Fin r) (Fin r) K)) :
    radical r K B = matrixEquiv r K (radicalGL B) :=
  rfl

theorem toMatrix'_radical (B : Multiplicative (Matrix (Fin r) (Fin r) K)) :
    LinearMap.toMatrix' ((radical r K B : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = blockUnip B.toAdd :=
  toMatrix'_matrixEquiv _

theorem radical_injective : Function.Injective (radical r K) := by
  intro B C h
  have h' := congrArg (fun g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
    LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) h
  simp only [toMatrix'_radical, blockUnip] at h'
  exact Multiplicative.toAdd.injective (Matrix.fromBlocks_inj.1 h').2.1

theorem radical_mem_posUnip {B : Matrix (Fin r) (Fin r) K} (hB : B ∈ altSubgroup r K) :
    radical r K (Multiplicative.ofAdd B) ∈ posUnip r K := by
  refine mem_posUnip_iff.2 ⟨1, B, Matrix.blockTriangular_one, fun i => by simp, hB.1, hB.2, ?_⟩
  rw [toMatrix'_radical, toAdd_ofAdd, blockUnip]
  simp

theorem leviGL_mul_radicalGL_mul_inv (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K) :
    leviGL A * radicalGL (Multiplicative.ofAdd B) * (leviGL A)⁻¹ =
      radicalGL (Multiplicative.ofAdd
        ((A : Matrix (Fin r) (Fin r) K) * B * (A : Matrix (Fin r) (Fin r) K)ᵀ)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, coe_leviGL, coe_leviGL, coe_radicalGL,
    coe_radicalGL, toAdd_ofAdd, toAdd_ofAdd, blockDiagInv, blockDiagInv, blockUnip, blockUnip,
    fromBlocks_multiply, fromBlocks_multiply, ← Matrix.coe_units_inv, ← Matrix.coe_units_inv,
    inv_inv]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Units.mul_inv]
  rw [← Matrix.transpose_mul, Units.mul_inv, transpose_one]

theorem levi_mul_radical_mul_inv (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K) :
    levi r K A * radical r K (Multiplicative.ofAdd B) * (levi r K A)⁻¹ =
      radical r K (Multiplicative.ofAdd
        ((A : Matrix (Fin r) (Fin r) K) * B * (A : Matrix (Fin r) (Fin r) K)ᵀ)) := by
  rw [levi_eq_matrixEquiv, radical_eq_matrixEquiv, radical_eq_matrixEquiv, ← map_inv, ← map_mul,
    ← map_mul, leviGL_mul_radicalGL_mul_inv]

theorem mem_posUnip_iff_levi_radical {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ posUnip r K ↔ ∃ (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K),
      (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
      (∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) ∧ B ∈ altSubgroup r K ∧
      g = levi r K A * radical r K (Multiplicative.ofAdd B) := by
  have hmat : ∀ (A : GL (Fin r) K) (B : Matrix (Fin r) (Fin r) K),
      LinearMap.toMatrix' ((levi r K A * radical r K (Multiplicative.ofAdd B) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * B) 0
          ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := fun A B => by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul, toMatrix'_levi,
      toMatrix'_radical, toAdd_ofAdd, fromBlocks_eq_blockDiagInv_mul]
  rw [mem_posUnip_iff]
  constructor
  · rintro ⟨A, C, hA, h1, hC, hd, hg⟩
    refine ⟨A, C, hA, h1, ⟨hC, hd⟩, ?_⟩
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    rw [hg, hmat]
  · rintro ⟨A, B, hA, h1, hB, rfl⟩
    exact ⟨A, B, hA, h1, hB.1, hB.2, hmat A B⟩

theorem eq_one_of_levi_eq_radical {A : GL (Fin r) K} {B : Matrix (Fin r) (Fin r) K}
    (h : levi r K A = radical r K (Multiplicative.ofAdd B)) : A = 1 ∧ B = 0 := by
  have h' := congrArg (fun g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
    LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) h
  simp only [toMatrix'_levi, toMatrix'_radical, blockDiagInv, blockUnip, toAdd_ofAdd] at h'
  obtain ⟨h1, h2, -, -⟩ := Matrix.fromBlocks_inj.1 h'
  exact ⟨Units.ext h1, h2.symm⟩

theorem det_eq_one_of_zmod_two (A : GL (Fin r) (ZMod 2)) :
    (A : Matrix (Fin r) (Fin r) (ZMod 2)).det = 1 := by
  have hu : IsUnit (A : Matrix (Fin r) (Fin r) (ZMod 2)).det := Matrix.isUnits_det_units A
  generalize (A : Matrix (Fin r) (Fin r) (ZMod 2)).det = d at hu
  fin_cases d
  · exact absurd hu not_isUnit_zero
  · rfl

variable (r) in
@[expose] def glToSL : GL (Fin r) (ZMod 2) →* SpecialLinearGroup (Fin r) (ZMod 2) where
  toFun A := ⟨A, det_eq_one_of_zmod_two A⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toGL_glToSL (A : GL (Fin r) (ZMod 2)) : SpecialLinearGroup.toGL (glToSL r A) = A :=
  Units.ext rfl

theorem mem_binaryAltMatrices_iff {B : Matrix (Fin r) (Fin r) (ZMod 2)} :
    B ∈ binaryAltMatrices r ↔ B ∈ altSubgroup r (ZMod 2) := by
  have h : -B = B := Matrix.ext fun i j => (Matrix.neg_apply B i j).trans (CharTwo.neg_eq _)
  rw [mem_binaryAltMatrices, mem_altSubgroup]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.trans h.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.trans h, h2⟩⟩

theorem congr_mem_binaryAltMatrices (A : Matrix (Fin r) (Fin r) (ZMod 2))
    {B : Matrix (Fin r) (Fin r) (ZMod 2)} (hB : B ∈ binaryAltMatrices r) :
    A * B * Aᵀ ∈ binaryAltMatrices r :=
  mem_binaryAltMatrices_iff.2 (congr_mem_altSubgroup A (mem_binaryAltMatrices_iff.1 hB))

@[expose] def altCongr (g : GL (Fin r) (ZMod 2)) (B : binaryAltMatrices r) :
    binaryAltMatrices r :=
  ⟨(g : Matrix (Fin r) (Fin r) (ZMod 2)) * B * (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ,
    congr_mem_binaryAltMatrices _ B.2⟩

theorem coe_altCongr (g : GL (Fin r) (ZMod 2)) (B : binaryAltMatrices r) :
    (altCongr g B : Matrix (Fin r) (Fin r) (ZMod 2)) =
      (g : Matrix (Fin r) (Fin r) (ZMod 2)) * B * (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ :=
  rfl

section Two

variable [CharP K 2]

variable (K) in
noncomputable abbrev castTwo : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

theorem castTwo_injective : Function.Injective (castTwo K) :=
  (castTwo K).injective

theorem map_mem_altSubgroup {B : Matrix (Fin r) (Fin r) (ZMod 2)} (hB : B ∈ binaryAltMatrices r) :
    B.map (castTwo K) ∈ altSubgroup r K := by
  refine ⟨?_, fun i => by rw [map_apply, hB.2 i, map_zero]⟩
  rw [← transpose_map, hB.1]
  exact Matrix.ext fun i j =>
    ((Matrix.neg_apply (B.map (castTwo K)) i j).trans (CharTwo.neg_eq _)).symm

variable (r K) in
@[expose] noncomputable def leviSLTwo (hr : 3 ≤ r) :
    SpecialLinearGroup (Fin r) (ZMod 2) →* orthElementaryGroup (quadPlus r K) :=
  (((levi r K).comp SpecialLinearGroup.toGL).comp
    (SpecialLinearGroup.map (castTwo K))).codRestrict _ fun _ =>
      levi_toGL_mem_orthElementaryGroup hr _

theorem coe_leviSLTwo (hr : 3 ≤ r) (A : SpecialLinearGroup (Fin r) (ZMod 2)) :
    (leviSLTwo r K hr A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      levi r K (SpecialLinearGroup.toGL (SpecialLinearGroup.map (castTwo K) A)) :=
  rfl

variable (r K) in
@[expose] noncomputable def leviTwo (hr : 3 ≤ r) :
    GL (Fin r) (ZMod 2) →* orthElementaryGroup (quadPlus r K) :=
  (leviSLTwo r K hr).comp (glToSL r)

theorem coe_leviTwo (hr : 3 ≤ r) (A : GL (Fin r) (ZMod 2)) :
    (leviTwo r K hr A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      levi r K (Matrix.GeneralLinearGroup.map (castTwo K) A) :=
  congrArg (levi r K) (Units.ext rfl)

theorem leviTwo_toGL (hr : 3 ≤ r) (A : SpecialLinearGroup (Fin r) (ZMod 2)) :
    leviTwo r K hr (SpecialLinearGroup.toGL A) = leviSLTwo r K hr A :=
  congrArg (leviSLTwo r K hr) (Subtype.ext rfl)

variable (r K) in
@[expose] noncomputable def radicalTwo :
    Multiplicative (binaryAltMatrices r) →* orthElementaryGroup (quadPlus r K) :=
  ((radical r K).comp (AddMonoidHom.toMultiplicative
    ((castTwo K).mapMatrix.toAddMonoidHom.comp (binaryAltMatrices r).subtype))).codRestrict _
      fun B => posUnip_le_orthElementaryGroup (radical_mem_posUnip (map_mem_altSubgroup B.toAdd.2))

theorem coe_radicalTwo (B : Multiplicative (binaryAltMatrices r)) :
    (radicalTwo r K B : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      radical r K (Multiplicative.ofAdd
        ((B.toAdd : Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K))) :=
  rfl

theorem leviSLTwo_injective (hr : 3 ≤ r) : Function.Injective (leviSLTwo r K hr) := by
  intro A B h
  have h' := levi_injective (congrArg Subtype.val h)
  apply Subtype.ext
  have h'' := congrArg (fun A : GL (Fin r) K => (A : Matrix (Fin r) (Fin r) K)) h'
  exact Matrix.map_injective castTwo_injective h''

theorem leviTwo_injective (hr : 3 ≤ r) : Function.Injective (leviTwo r K hr) := by
  intro A B h
  simpa [toGL_glToSL] using congrArg SpecialLinearGroup.toGL (leviSLTwo_injective hr h)

theorem radicalTwo_injective : Function.Injective (radicalTwo r K) := by
  intro B C h
  have h' := radical_injective (congrArg Subtype.val h)
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact Matrix.map_injective castTwo_injective (Multiplicative.ofAdd.injective h')

theorem leviTwo_mul_radicalTwo_mul_inv (hr : 3 ≤ r) (g : GL (Fin r) (ZMod 2))
    (B : binaryAltMatrices r) :
    leviTwo r K hr g * radicalTwo r K (Multiplicative.ofAdd B) * (leviTwo r K hr g)⁻¹ =
      radicalTwo r K (Multiplicative.ofAdd (altCongr g B)) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviTwo, coe_radicalTwo,
    coe_radicalTwo, levi_mul_radical_mul_inv]
  congr 2
  rw [toAdd_ofAdd, toAdd_ofAdd, coe_altCongr, Matrix.map_mul, Matrix.map_mul, transpose_map]
  rfl

variable [Finite K]

theorem castTwo_bijective (hK : Nat.card K = 2) : Function.Bijective (castTwo K) :=
  castTwo_injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])

theorem exists_sylow_leviSLTwo_radicalTwo (hr : 3 ≤ r) (hK : Nat.card K = 2) :
    ∃ S : Sylow 2 (orthElementaryGroup (quadPlus r K)),
      (∀ g ∈ (S : Subgroup (orthElementaryGroup (quadPlus r K))),
        ∃ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (leviSLTwo r K hr),
          ∃ b ∈ (radicalTwo r K).range, g = a * b) ∧
      (LinearFlag.unitriangular r (ZMod 2)).map (leviSLTwo r K hr) ⊓ (radicalTwo r K).range =
        ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := r) (K := K) 2 (by omega)
    fun a ha => map_flag_top_ne_Xstar hr ha
  set e : ZMod 2 ≃+* K := RingEquiv.ofBijective (castTwo K) (castTwo_bijective hK) with he
  have hee : ∀ x : K, castTwo K (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨S, fun g hg => ?_, ?_⟩
  · rw [hS, Subgroup.mem_subgroupOf] at hg
    obtain ⟨A, B, hA, h1, hB, hg⟩ := mem_posUnip_iff_levi_radical.1 hg
    set A₀ : Matrix (Fin r) (Fin r) (ZMod 2) := (A : Matrix (Fin r) (Fin r) K).map e.symm
    set B₀ : Matrix (Fin r) (Fin r) (ZMod 2) := B.map e.symm
    have hA₀ : A₀.map (castTwo K) = A := Matrix.ext fun i j => hee _
    have hB₀ : B₀.map (castTwo K) = B := Matrix.ext fun i j => hee _
    have hdet : A₀.det = 1 := by
      apply castTwo_injective (K := K)
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hA₀, map_one,
        Matrix.det_of_isUpperTriangular hA]
      exact Finset.prod_eq_one fun i _ => h1 i
    set A₁ : SpecialLinearGroup (Fin r) (ZMod 2) := ⟨A₀, hdet⟩
    have hA₁ : A₁ ∈ LinearFlag.unitriangular r (ZMod 2) := by
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · change e.symm ((A : Matrix (Fin r) (Fin r) K) i j) = 0
        rw [hA hij, map_zero]
      · change e.symm ((A : Matrix (Fin r) (Fin r) K) i i) = 1
        rw [h1 i, map_one]
    have hB₁ : B₀ ∈ binaryAltMatrices r := by
      refine mem_binaryAltMatrices_iff.2 ⟨?_, fun i => ?_⟩
      · ext i j
        have hji : B j i = -B i j := by
          have := congrFun (congrFun hB.1 i) j
          simpa using this
        change e.symm (B j i) = -e.symm (B i j)
        rw [hji, map_neg]
      · change e.symm (B i i) = 0
        rw [hB.2 i, map_zero]
    refine ⟨leviSLTwo r K hr A₁, ⟨A₁, hA₁, rfl⟩,
      radicalTwo r K (Multiplicative.ofAdd ⟨B₀, hB₁⟩), ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, coe_leviSLTwo, coe_radicalTwo, hg]
    congr 2
    · exact Units.ext hA₀.symm
    · rw [toAdd_ofAdd]
      exact congrArg Multiplicative.ofAdd hB₀.symm
  · rw [eq_bot_iff]
    rintro x ⟨⟨A₁, -, rfl⟩, ⟨B, hB⟩⟩
    rw [Subgroup.mem_bot]
    have h := congrArg Subtype.val hB
    rw [coe_radicalTwo, coe_leviSLTwo] at h
    obtain ⟨hA1, -⟩ := eq_one_of_levi_eq_radical h.symm
    apply Subtype.ext
    rw [coe_leviSLTwo, hA1, map_one]
    rfl

end Two

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
