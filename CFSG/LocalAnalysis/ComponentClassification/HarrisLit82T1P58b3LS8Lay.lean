module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Mat
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQOrthAll
public import CFSG.RankThree.PartOne.KLC.ThreePoint
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQOrth
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S8

open Matrix CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.HarrisLit.T1.F3FG
open scoped commutatorElement

theorem exists_mul_self_eq_map_mul_inv {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (μ : Kˣ) : ∃ ν : Kˣ, Units.map σ.toRingHom.toMonoidHom μ * μ⁻¹ = ν * ν := by
  set S := (powMonoidHom 2 : Kˣ →* Kˣ).range with hS
  have hσS : ∀ x : Kˣ, Units.map σ.toRingHom.toMonoidHom x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Units.map σ.symm.toRingHom.toMonoidHom y, Units.ext ?_⟩
      have h := congrArg (fun u : Kˣ => σ.symm (u : K)) hy
      simpa [powMonoidHom_apply] using h
    · rintro ⟨y, rfl⟩
      exact ⟨Units.map σ.toRingHom.toMonoidHom y, by simp [powMonoidHom_apply]⟩
  have hidx : S.index ∣ 2 := by
    rw [hS, IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_dvd_right _ _
  have hmem : Units.map σ.toRingHom.toMonoidHom μ * μ⁻¹ ∈ S := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.mem_top _
    · rw [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff, hσS]
  obtain ⟨ν, hν⟩ := hmem
  exact ⟨ν, by rw [← hν, powMonoidHom_apply, sq]⟩

variable (K : Type) [Field K]

theorem coordinateQuadPlus_map (σ : K ≃+* K) (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K (fun i => σ (v i)) = σ (coordinateQuadPlus 4 K v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply, map_sum]
  simp only [map_mul]

@[expose] def fieldPair : (K ≃+* K) →* similarityPairs (coordinateQuadPlus 4 K) :=
  (SemidirectProduct.inr : (K ≃+* K) →* coordinateSemilinearGroup (2 * 4) K).codRestrict _
    fun σ => ⟨1, fun v => by
      rw [coordinateSemilinearMap_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
        Units.val_one, one_mulVec, Units.val_one, one_mul, coordinateQuadPlus_map]⟩

@[expose] def dilHom : Kˣ →* GL (Fin 4 ⊕ Fin 4) K where
  toFun := dil K
  map_one' := by
    rw [dil, ← map_one (diagU (K := K) (ι := Fin 4 ⊕ Fin 4))]
    congr 1
    funext x
    cases x <;> rfl
  map_mul' := dil_mul

@[expose] def dilPair : Kˣ →* similarityPairs (coordinateQuadPlus 4 K) :=
  ((SemidirectProduct.inl : GL (Fin (2 * 4)) K →* coordinateSemilinearGroup (2 * 4) K).comp
      ((R8 K).toMonoidHom.comp (dilHom K))).codRestrict _
    fun μ => ⟨μ, fun v => by
      change coordinateQuadPlus 4 K (matrixLinearEquiv (R8 K (dil K μ)) v) =
        (μ : K) * (1 : K ≃+* K) (coordinateQuadPlus 4 K v)
      rw [coordinateQuadPlus_R8 (quadPlus_dil μ)]
      rfl⟩

@[expose] def torIso (a : Fin 4 → Kˣ) : matrixIsometries (coordinateQuadPlus 4 K) :=
  ⟨R8 K (tor K a), R8_mem_matrixIsometries (quadPlus_tor a)⟩

@[expose] def wIso : matrixIsometries (coordinateQuadPlus 4 K) :=
  ⟨R8 K (wU K), R8_mem_matrixIsometries quadPlus_wU⟩

@[expose] def swapIso : matrixIsometries (coordinateQuadPlus 4 K) :=
  ⟨R8 K (plusSwapMatrix 4 K (by norm_num)), R8_mem_matrixIsometries fun v => by
    rw [coe_quadPlus]
    exact statedQuadPlus_plusSwapMatrix_mulVec 4 K (by norm_num) v⟩

theorem isometryDet_swapIso : isometryDet (coordinateQuadPlus 4 K) (swapIso K) = -1 := by
  change GeneralLinearGroup.det (R8 K (plusSwapMatrix 4 K (by norm_num))) = -1
  rw [det_R8, det_plusSwapMatrix]

theorem torIso_eq_commutator (ν : Kˣ) :
    torIso K (fun _ => ν) = ⁅torIso K ![1, ν, 1, ν], wIso K⁆ := by
  apply Subtype.ext
  change R8 K (tor K fun _ => ν) = ⁅R8 K (tor K ![1, ν, 1, ν]), R8 K (wU K)⁆
  rw [← commutator_torAlt_wU, map_commutatorElement]

local notation "κ" => matrixProjectiveConjugationHom (coordinateQuadPlus 4 K)
local notation "P" => matrixProjectiveDerived (coordinateQuadPlus 4 K)

theorem isometryConjugationHom_eq (o : matrixIsometries (coordinateQuadPlus 4 K)) :
    isometryConjugationHom (coordinateQuadPlus 4 K) o = κ (matrixIsometryInclusion _ o) := rfl

theorem kappa_dilPair_mul_self_mem_inner (ν : Kˣ) : κ (dilPair K (ν * ν)) ∈ inner P := by
  have h : κ (dilPair K (ν * ν)) = κ (matrixIsometryInclusion _ (torIso K fun _ => ν)) := by
    refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar _ ν ?_ rfl
    change R8 K (dil K (ν * ν)) = R8 K (tor K fun _ => ν) * GeneralLinearGroup.scalar _ ν
    rw [dil_mul_self, map_mul, reindexMatrixEquiv_scalar]
    have hc : GeneralLinearGroup.scalar (Fin (2 * 4)) ν ∈ Subgroup.center (GL (Fin (2 * 4)) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨ν, rfl⟩
    exact (Subgroup.mem_center_iff.mp hc _).symm
  rw [h, ← isometryConjugationHom_eq, torIso_eq_commutator, inner_eq_map_commutator]
  exact Subgroup.mem_map_of_mem _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem fieldPair_mul_dilPair_mul_inv (σ : K ≃+* K) (μ : Kˣ) :
    fieldPair K σ * dilPair K μ * (fieldPair K σ)⁻¹ =
      dilPair K (Units.map σ.toRingHom.toMonoidHom μ) := by
  apply Subtype.ext
  change SemidirectProduct.inr σ * SemidirectProduct.inl (R8 K (dil K μ)) *
      (SemidirectProduct.inr σ)⁻¹ = SemidirectProduct.inl (R8 K (dil K _))
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  congr 1
  change glFieldAut (Fin (2 * 4)) K σ (R8 K (dil K μ)) = _
  rw [glFieldAut_R8, glFieldAut_dil]

theorem fieldPair_mul_swap_mul_inv (σ : K ≃+* K) :
    fieldPair K σ * matrixIsometryInclusion _ (swapIso K) * (fieldPair K σ)⁻¹ =
      matrixIsometryInclusion _ (swapIso K) := by
  apply Subtype.ext
  change SemidirectProduct.inr σ * SemidirectProduct.inl (R8 K (plusSwapMatrix 4 K _)) *
      (SemidirectProduct.inr σ)⁻¹ = SemidirectProduct.inl (R8 K (plusSwapMatrix 4 K _))
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  congr 1
  change glFieldAut (Fin (2 * 4)) K σ (R8 K (plusSwapMatrix 4 K _)) = _
  rw [glFieldAut_R8, glFieldAut_plusSwapMatrix]

theorem commutator_fieldPair_dilPair_mem_inner [Finite K] (σ : K ≃+* K) (μ : Kˣ) :
    ⁅κ (fieldPair K σ), κ (dilPair K μ)⁆ ∈ inner P := by
  obtain ⟨ν, hν⟩ := exists_mul_self_eq_map_mul_inv σ μ
  have h : ⁅fieldPair K σ, dilPair K μ⁆ = dilPair K (ν * ν) := by
    rw [commutatorElement_def, fieldPair_mul_dilPair_mul_inv, ← map_inv, ← map_mul, hν]
  rw [← map_commutatorElement, h]
  exact kappa_dilPair_mul_self_mem_inner K ν

theorem isometryDet_eq_neg_one
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus 4 K)).Nondegenerate)
    (o : matrixIsometries (coordinateQuadPlus 4 K)) (ho : isometryDet _ o ≠ 1) :
    isometryDet _ o = -1 := by
  have h : isometryDet _ o ^ 2 = 1 ^ 2 := by rw [one_pow]; exact isometryDet_sq _ hnd o
  exact (Units.eq_or_eq_neg_of_sq_eq_sq _ _ h).resolve_left ho

@[expose] def commSub {A : Type*} [Group A] (N : Subgroup A) [N.Normal] (u : A) : Subgroup A :=
  (Subgroup.centralizer {QuotientGroup.mk' N u}).comap (QuotientGroup.mk' N)

theorem mem_commSub {A : Type*} [Group A] (N : Subgroup A) [N.Normal] (u x : A) :
    x ∈ commSub N u ↔ ⁅u, x⁆ ∈ N := by
  rw [commSub, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact eq_comm

theorem commutator_fieldPair_mem_inner [Finite K] (h2 : ringChar K ≠ 2)
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus 4 K)).Nondegenerate)
    (hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 4)
    (σ : K ≃+* K) {d : MulAut P} (hd : d ∈ (linearConjugationHom (coordinateQuadPlus 4 K)).range) :
    ⁅κ (fieldPair K σ), d⁆ ∈ inner P := by
  set u := κ (fieldPair K σ) with hu
  rw [← mem_commSub]
  have hneg : ∃ A : matrixIsometries (coordinateQuadPlus 4 K), isometryDet _ A ≠ 1 :=
    ⟨swapIso K, by
      rw [isometryDet_swapIso]
      exact fun h => Ring.neg_one_ne_one_of_char_ne_two h2 (congrArg Units.val h)⟩
  have : Finite (MulAut P) :=
    Finite.of_injective (fun e : MulAut P => (e : P → P)) DFunLike.coe_injective
  have hS : ∀ s ∈ specialIsometries (coordinateQuadPlus 4 K),
      isometryConjugationHom _ s ∈ commSub (inner P) u := by
    intro s hs
    rw [mem_commSub]
    have hmem : isometryConjugationHom _ s ∈
        (specialIsometries (coordinateQuadPlus 4 K)).map (isometryConjugationHom _) :=
      Subgroup.mem_map_of_mem _ hs
    refine CFSG.RankThree.PartOne.KLC.commutator_mem_of_relIndex_le_two _ _ ?_
      (relIndex_inner_specialRange_le_two _ hab hneg) hmem ?_
    · rw [inner_eq_map_commutator]
      exact Subgroup.map_mono (Abelianization.commutator_subset_ker (isometryDet _))
    · obtain ⟨t, ht, hts⟩ := (specialPairs_normal (coordinateQuadPlus 4 K)).conj_mem
        (matrixIsometryInclusion _ s) ⟨s, hs, rfl⟩ (fieldPair K σ)
      refine ⟨t, ht, ?_⟩
      rw [isometryConjugationHom_eq, hts, hu, isometryConjugationHom_eq, map_mul, map_mul,
        map_inv]
  have hswap : isometryConjugationHom _ (swapIso K) ∈ commSub (inner P) u := by
    rw [mem_commSub, isometryConjugationHom_eq, hu, ← map_commutatorElement, commutatorElement_def,
      fieldPair_mul_swap_mul_inv, mul_inv_cancel, map_one]
    exact one_mem _
  have hO : ∀ o, isometryConjugationHom _ o ∈ commSub (inner P) u := by
    intro o
    by_cases ho : isometryDet _ o = 1
    · exact hS o ho
    · have h1 : (swapIso K)⁻¹ * o ∈ specialIsometries (coordinateQuadPlus 4 K) := by
        change isometryDet _ ((swapIso K)⁻¹ * o) = 1
        rw [map_mul, map_inv, isometryDet_swapIso, isometryDet_eq_neg_one K hnd o ho, inv_neg,
          inv_one, neg_one_mul, neg_neg]
      have h2 := mul_mem hswap (hS _ h1)
      rwa [← map_mul, mul_inv_cancel_left] at h2
  obtain ⟨g, rfl⟩ := hd
  set μ := multiplierHom (coordinateQuadPlus 4 K) hQ g with hμ
  have hiso : (dilPair K μ⁻¹ * g.val).val.left ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
    rw [mem_matrixIsometries_iff]
    intro v
    have hg : (g.val.val.right) = 1 := (mem_linearSimilarityPairs_iff _ g.val).mp g.property
    have hl : (dilPair K μ⁻¹ * g.val).val.left = R8 K (dil K μ⁻¹) * g.val.val.left := by
      change R8 K (dil K μ⁻¹) * glFieldAut (Fin (2 * 4)) K 1 g.val.val.left = _
      rw [map_one]
      rfl
    rw [hl, matrixLinearEquiv_mul, LinearEquiv.mul_apply, coordinateQuadPlus_R8 (quadPlus_dil μ⁻¹),
      multiplierHom_spec _ hQ, ← hμ, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  have hright : (dilPair K μ⁻¹ * g.val).val.right = 1 := by
    change (1 : K ≃+* K) * g.val.val.right = 1
    rw [(mem_linearSimilarityPairs_iff _ g.val).mp g.property, one_mul]
  set o : matrixIsometries (coordinateQuadPlus 4 K) := ⟨_, hiso⟩ with ho
  have hgo : g.val = dilPair K μ * matrixIsometryInclusion _ o := by
    have h : matrixIsometryInclusion _ o = dilPair K μ⁻¹ * g.val :=
      Subtype.ext (SemidirectProduct.ext rfl hright.symm)
    rw [h, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hdil : κ (dilPair K μ) ∈ commSub (inner P) u := by
    rw [mem_commSub]
    exact commutator_fieldPair_dilPair_mem_inner K σ μ
  change κ g.val ∈ commSub (inner P) u
  rw [hgo, map_mul]
  exact mul_mem hdil (hO o)

theorem relIndex_inner_linearRange_le_eight [Finite K] (h2 : ringChar K ≠ 2)
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus 4 K)).Nondegenerate)
    (hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 4) :
    (inner P).relIndex (linearConjugationHom (coordinateQuadPlus 4 K)).range ≤ 8 := by
  have hneg : ∃ A : matrixIsometries (coordinateQuadPlus 4 K), isometryDet _ A ≠ 1 :=
    ⟨swapIso K, by
      rw [isometryDet_swapIso]
      exact fun h => Ring.neg_one_ne_one_of_char_ne_two h2 (congrArg Units.val h)⟩
  have h1 : inner P ≤ (specialIsometries (coordinateQuadPlus 4 K)).map
      (isometryConjugationHom _) := by
    rw [inner_eq_map_commutator]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker (isometryDet _))
  have h2' : (specialIsometries (coordinateQuadPlus 4 K)).map (isometryConjugationHom _) ≤
      (isometryConjugationHom (coordinateQuadPlus 4 K)).range := Subgroup.map_le_range _ _
  have h3 := isometryConjugationHom_range_le (coordinateQuadPlus 4 K)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 (h2'.trans h3),
    ← Subgroup.relIndex_mul_relIndex _ _ _ h2' h3]
  have e1 := relIndex_inner_specialRange_le_two _ hab hneg
  have e2 := relIndex_specialRange_isometryRange_le_two _ hnd
  have e3 := relIndex_isometryRange_linearRange_le_two _ hQ
  calc _ ≤ 2 * (2 * 2) := Nat.mul_le_mul e1 (Nat.mul_le_mul e2 e3)
    _ = 8 := by norm_num

end CFSG.ComponentClassification.HarrisLit.T1.S8
