module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Lay
public import
  CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotentInvariant

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S8

open Matrix CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable (K : Type) [Field K]

local notation "κ" => matrixProjectiveConjugationHom (coordinateQuadPlus 4 K)

@[expose] def Rd8 : StatedOmega (StatedQuadPlus 4 K) ≃* matrixDerived (coordinateQuadPlus 4 K) :=
  statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)

theorem Rd8_val (A : StatedOmega (StatedQuadPlus 4 K)) : (Rd8 K A).val = R8 K A.val :=
  statedDerivedReindexEquiv_val _ _ _ A

theorem Rd8_symm_val (M : matrixDerived (coordinateQuadPlus 4 K)) :
    ((Rd8 K).symm M).val = (R8 K).symm M.val :=
  statedDerivedReindexEquiv_symm_val _ _ _ M

theorem plusCoordinateEquiv_mk (A : StatedOmega (StatedQuadPlus 4 K)) :
    plusCoordinateEquiv 4 K (QuotientGroup.mk' _ A) =
      matrixProjectiveProjection (coordinateQuadPlus 4 K) (Rd8 K A) :=
  statedProjectiveReindexEquiv_mk _ _ _ A

theorem plusCoordinateEquiv_symm_mk (M : matrixDerived (coordinateQuadPlus 4 K)) :
    (plusCoordinateEquiv 4 K).symm (matrixProjectiveProjection (coordinateQuadPlus 4 K) M) =
      QuotientGroup.mk' _ ((Rd8 K).symm M) :=
  statedProjectiveReindexEquiv_symm_mk _ _ _ M

theorem kappa_swapIso :
    κ (matrixIsometryInclusion _ (swapIso K)) =
      MulAut.congr (plusCoordinateEquiv 4 K) (plusSwapAut 4 K (by norm_num)) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (plusCoordinateEquiv 4 K).surjective x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [automorphismTransport_apply, MulEquiv.symm_apply_apply, plusSwapAut_mk_conj,
    plusCoordinateEquiv_mk, plusCoordinateEquiv_mk]
  change matrixProjectiveConjugation (coordinateQuadPlus 4 K)
    (matrixIsometryInclusion _ (swapIso K)) (matrixProjectiveProjection _ _) = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val, Rd8_val, Rd8_val]
  change R8 K (plusSwapMatrix 4 K _) * glFieldAut (Fin (2 * 4)) K 1 (R8 K A.val) *
      (R8 K (plusSwapMatrix 4 K _))⁻¹ =
    R8 K (plusSwapMatrix 4 K _ * A.val * (plusSwapMatrix 4 K _)⁻¹)
  rw [map_one, MulAut.one_apply, map_mul, map_mul, map_inv]

theorem kappa_swapIso_smul_plusCX :
    κ (matrixIsometryInclusion _ (swapIso K)) • plusCX 4 K = plusCXstar 4 K (by norm_num) := by
  rw [kappa_swapIso, plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_flag]

theorem kappa_swapIso_smul_plusCXstar :
    κ (matrixIsometryInclusion _ (swapIso K)) • plusCXstar 4 K (by norm_num) = plusCX 4 K := by
  rw [kappa_swapIso, plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_Xstar]

theorem plusCX_ne_plusCXstar [Finite K] : plusCX 4 K ≠ plusCXstar 4 K (by norm_num) := by
  rw [plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy]
  exact fun h => conjugacyFamily_flag_ne_Xstar 4 K (by norm_num)
    ((familyTransport (plusCoordinateEquiv 4 K)).injective h)

theorem exists_fieldPair_transport_mk (σ : K ≃+* K) (A : StatedOmega (StatedQuadPlus 4 K)) :
    ∃ B : StatedOmega (StatedQuadPlus 4 K),
      (MulAut.congr (plusCoordinateEquiv 4 K)).symm (κ (fieldPair K σ)) (QuotientGroup.mk' _ A) =
        QuotientGroup.mk' _ B ∧ B.val = glFieldAut (Fin 4 ⊕ Fin 4) K σ A.val := by
  refine ⟨(Rd8 K).symm (matrixDerivedConjugation (coordinateQuadPlus 4 K) (fieldPair K σ)
    (Rd8 K A)), ?_, ?_⟩
  · rw [automorphismTransport_symm_apply, plusCoordinateEquiv_mk]
    change (plusCoordinateEquiv 4 K).symm (matrixProjectiveConjugation (coordinateQuadPlus 4 K)
      (fieldPair K σ) (matrixProjectiveProjection _ _)) = _
    rw [matrixProjectiveConjugation_mk, plusCoordinateEquiv_symm_mk]
  · rw [Rd8_symm_val, matrixDerivedConjugation_val, Rd8_val]
    change (R8 K).symm (1 * glFieldAut (Fin (2 * 4)) K σ (R8 K A.val) * 1⁻¹) = _
    rw [one_mul, inv_one, mul_one, glFieldAut_R8, MulEquiv.symm_apply_apply]

theorem map_glFieldAut_eq {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (σ : K ≃+* K)
    (hW : ∀ v ∈ W, (fun i => σ (v i)) ∈ W) (hW' : ∀ v ∈ W, (fun i => σ.symm (v i)) ∈ W)
    {A : GL (Fin 4 ⊕ Fin 4) K} (hA : W.map (toLinEquiv _ K A).toLinearMap = W) :
    W.map (toLinEquiv _ K (glFieldAut _ K σ A)).toLinearMap = W := by
  have hle : W.map (toLinEquiv _ K (glFieldAut _ K σ A)).toLinearMap ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : (A : Matrix _ _ K) *ᵥ (fun i => σ.symm (v i)) ∈ W := by
      rw [← hA]
      exact ⟨_, hW' v hv, rfl⟩
    have h2 := hW _ h1
    convert h2 using 1
    funext i
    simp only [LinearEquiv.coe_coe, toLinEquiv_apply, mulVec, dotProduct, map_sum, map_mul,
      RingEquiv.apply_symm_apply]
    rfl
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

theorem fun_mem_flag (τ : K ≃+* K) {v : Fin 4 ⊕ Fin 4 → K} (hv : v ∈ flag 4 K 4) :
    (fun i => τ (v i)) ∈ flag 4 K 4 := by
  rw [mem_flag_iff_coord] at hv ⊢
  exact ⟨fun k => by rw [hv.1 k, map_zero], fun k hk => by rw [hv.2 k hk, map_zero]⟩

theorem fun_mem_Xstar (τ : K ≃+* K) {v : Fin 4 ⊕ Fin 4 → K} (hv : v ∈ Xstar 4 K (by norm_num)) :
    (fun i => τ (v i)) ∈ Xstar 4 K (by norm_num) := by
  rw [mem_Xstar] at hv ⊢
  exact ⟨by rw [hv.1, map_zero], fun k hk => by rw [hv.2 k hk, map_zero]⟩

theorem map_stabilizer_fieldPair [Finite K] (σ : K ≃+* K) {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hW : ∀ τ : K ≃+* K, ∀ v ∈ W, (fun i => τ (v i)) ∈ W) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).map
        ((MulAut.congr (plusCoordinateEquiv 4 K)).symm (κ (fieldPair K σ))).toMonoidHom =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W := by
  set β := (MulAut.congr (plusCoordinateEquiv 4 K)).symm (κ (fieldPair K σ)) with hβ
  have hle : (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W).map β.toMonoidHom ≤
      statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hx' : A ∈ statedDerivedSubspaceStabilizer (StatedQuadPlus 4 K) W :=
      (mem_statedProjectiveSubspaceStabilizer_mk _ W A).mp hx
    obtain ⟨B, hB, hBA⟩ := exists_fieldPair_transport_mk K σ A
    change β (QuotientGroup.mk' _ A) ∈ _
    rw [hB]
    refine (mem_statedProjectiveSubspaceStabilizer_mk _ W B).mpr ?_
    rw [mem_statedDerivedSubspaceStabilizer, hBA]
    rw [mem_statedDerivedSubspaceStabilizer] at hx'
    exact map_glFieldAut_eq K σ (hW σ) (hW σ.symm) hx'
  have : Finite (StatedProj (StatedOmega (StatedQuadPlus 4 K))) :=
    Finite.of_equiv _ (plusCoordinateEquiv 4 K).symm.toEquiv
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective β.injective]

theorem kappa_fieldPair_smul_plusCX [Finite K] (σ : K ≃+* K) :
    κ (fieldPair K σ) • plusCX 4 K = plusCX 4 K := by
  have h : κ (fieldPair K σ) = MulAut.congr (plusCoordinateEquiv 4 K)
      ((MulAut.congr (plusCoordinateEquiv 4 K)).symm (κ (fieldPair K σ))) :=
    (MulEquiv.apply_symm_apply _ _).symm
  rw [plusCX, ← familyTransport_conjugacy, h, ← familyTransport_automorphism,
    conjugacyFamily_covariance, map_stabilizer_fieldPair K σ fun τ v hv => fun_mem_flag K τ hv]

theorem kappa_fieldPair_smul_plusCXstar [Finite K] (σ : K ≃+* K) :
    κ (fieldPair K σ) • plusCXstar 4 K (by norm_num) = plusCXstar 4 K (by norm_num) := by
  have h : κ (fieldPair K σ) = MulAut.congr (plusCoordinateEquiv 4 K)
      ((MulAut.congr (plusCoordinateEquiv 4 K)).symm (κ (fieldPair K σ))) :=
    (MulEquiv.apply_symm_apply _ _).symm
  rw [plusCXstar, ← familyTransport_conjugacy, h, ← familyTransport_automorphism,
    conjugacyFamily_covariance, map_stabilizer_fieldPair K σ fun τ v hv => fun_mem_Xstar K τ hv]

end CFSG.ComponentClassification.HarrisLit.T1.S8
