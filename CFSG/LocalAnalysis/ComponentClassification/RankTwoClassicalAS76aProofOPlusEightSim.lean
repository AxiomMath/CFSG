module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusEight
public import CFSG.RankThree.SteinbergR3ECAEvenD4Centralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Image

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem exists_semilinear_statedProj_of_mem (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (β : MulAut (StatedProj (StatedOmega Q₀)))
    (hβ : (statedProjectiveReindexEquiv eI Q hQ).symm.trans
      (β.trans (statedProjectiveReindexEquiv eI Q hQ)) ∈
        matrixProjectiveImage (reindexQuadraticForm eI Q)) :
    ∃ (σ : K ≃+* K) (A : GL ι K) (μ : K), μ ≠ 0 ∧
      (∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q₀ v)) ∧
      ∀ g : StatedOmega Q₀, ∃ hg : A * glAut σ (g : GL ι K) * A⁻¹ ∈ StatedOmega Q₀,
        β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
  obtain ⟨s, hsβ⟩ := (mem_matrixProjectiveImage_iff (reindexQuadraticForm eI Q) _).mp hβ
  obtain ⟨μ, hμ⟩ := s.2
  set A : GL ι K := (reindexMatrixEquiv eI).symm s.val.left
  have hAs : reindexMatrixEquiv eI A = s.val.left := MulEquiv.apply_symm_apply _ _
  refine ⟨s.val.right, A, μ, μ.ne_zero, fun v => ?_, fun g => ?_⟩
  · have h1 := hμ (reindexVectorEquiv eI v)
    have h2 : coordinateSemilinearMap s.val (reindexVectorEquiv eI v) =
        reindexVectorEquiv eI ((A : Matrix ι ι K) *ᵥ fun i => s.val.right (v i)) := by
      rw [← reindexMatrixEquiv_mulVec, hAs, coordinateSemilinearMap_apply]
      rfl
    rw [h2, reindexQuadraticForm_map, reindexQuadraticForm_map, hQ] at h1
    exact h1
  · obtain ⟨x, hx⟩ : ∃ x, x = matrixDerivedConjugation (reindexQuadraticForm eI Q) s
        (statedDerivedReindexEquiv eI Q hQ g) := ⟨_, rfl⟩
    have hxv : (x : GL (Fin d) K) =
        reindexMatrixEquiv eI (A * glAut s.val.right (g : GL ι K) * A⁻¹) := by
      rw [hx, matrixDerivedConjugation_val, map_mul, map_mul, map_inv, hAs,
        reindexMatrixEquiv_glAut, statedDerivedReindexEquiv_val]
    have hg' : (((statedDerivedReindexEquiv eI Q hQ).symm x : StatedOmega Q₀) : GL ι K) =
        A * glAut s.val.right (g : GL ι K) * A⁻¹ := by
      rw [statedDerivedReindexEquiv_symm_val, hxv, MulEquiv.symm_apply_apply]
    refine ⟨hg' ▸ ((statedDerivedReindexEquiv eI Q hQ).symm x).2, ?_⟩
    have h1 : statedProjectiveReindexEquiv eI Q hQ (β (QuotientGroup.mk g)) =
        matrixProjectiveProjection (reindexQuadraticForm eI Q) x := by
      have h2 := congrArg (fun φ => φ (statedProjectiveReindexEquiv eI Q hQ
        (QuotientGroup.mk' _ g))) hsβ
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
      change statedProjectiveReindexEquiv eI Q hQ (β (QuotientGroup.mk' _ g)) = _
      rw [← h2, statedProjectiveReindexEquiv_mk, matrixProjectiveConjugation_mk, hx]
    have h3 : β (QuotientGroup.mk g) =
        QuotientGroup.mk' _ ((statedDerivedReindexEquiv eI Q hQ).symm x) := by
      rw [← statedProjectiveReindexEquiv_symm_mk eI Q hQ x, ← h1, MulEquiv.symm_apply_apply]
    rw [h3]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hg')

end Image

section Swap

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def oSwapSL : SL(2, K) :=
  ⟨swapM, by rw [det_fin_two]; simp [swapM, CharTwo.neg_eq]⟩

theorem rhoTwoMat_mul_rhoOneMat_oSwapSL :
    rhoTwoMat (oSwapSL : SL(2, K)) * rhoOneMat oSwapSL =
      (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hJ : ((oSwapSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = swapM := rfl
  have h00 : (swapM : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by simp [swapM]
  have h01 : (swapM : Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := by simp [swapM]
  have h10 : (swapM : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by simp [swapM]
  have h11 : (swapM : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by simp [swapM]
  rw [rhoTwoMat_apply, rhoOneMat_apply, hJ, adjugate_transpose_eq, swapM_mul_swapM,
    Matrix.one_mul, h00, h01, h10, h11, zero_smul, one_smul, fromBlocks_multiply]
  simp [swapM_mul_swapM]

theorem exists_oDSwap (hSL : commutator SL(2, K) = ⊤) :
    ∃ Y : StatedOmega (StatedQuadPlus 2 K),
      ((Y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 1 1 0 := by
  refine ⟨⟨rhoTwoMat.toHomUnits oSwapSL * rhoOneMat.toHomUnits oSwapSL, mul_mem
    (mem_statedOmega_of_perfect hSL _ (fun A => Subgroup.subset_closure fun v =>
      quadPlus_two_rhoTwo A v) _)
    (mem_statedOmega_of_perfect hSL _ (fun B => Subgroup.subset_closure fun v =>
      quadPlus_two_rhoOne B v) _)⟩, ?_⟩
  change rhoTwoMat oSwapSL * rhoOneMat oSwapSL = _
  exact rhoTwoMat_mul_rhoOneMat_oSwapSL

theorem oblk_oDSwap_mulVec (x : Fin (2 + 2) ⊕ Fin (2 + 2) → K) :
    oblk (plusOe 2) (fromBlocks 0 1 1 0) 1 *ᵥ x =
      x + (x (.inr 0) + x (.inl 0)) • (Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1) +
        (x (.inr 1) + x (.inl 1)) • (Pi.single (.inl 1) 1 + Pi.single (.inr 1) 1) := by
  funext j
  obtain ⟨k, rfl⟩ := (plusOe 2).surjective j
  rcases k with (i | i) | (t | t)
  · rw [oblk_mulVec_inl]
    fin_cases i <;> simp [fromBlocks_mulVec, plusOe] <;>
      linear_combination -x (.inl _) * CharTwo.two_eq_zero (R := K)
  · rw [oblk_mulVec_inl]
    fin_cases i <;> simp [fromBlocks_mulVec, plusOe] <;>
      linear_combination -x (.inr _) * CharTwo.two_eq_zero (R := K)
  · rw [oblk_mulVec_inr, one_mulVec]
    fin_cases t <;> simp [plusOe]
  · rw [oblk_mulVec_inr, one_mulVec]
    fin_cases t <;> simp [plusOe]

end Swap

open CFSG.RankThree.EvenD4Centralizer in
theorem omegaPlusEightThreeA1Similarity : OmegaPlusEightThreeA1Similarity := by
  intro K _ _ _ _ hSL β _ hL
  obtain ⟨f, hf, hK⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_card_eq_pow K
  rw [ringChar.eq K 2] at hK
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4
      2 f := ⟨⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨Y, hY⟩ := exists_oDSwap (K := K) hSL
  set g₀ := oKappa (plusOe 2) (statedQuadPlus_plusOe 2) Y with hg₀
  have hfix : β (QuotientGroup.mk g₀) = QuotientGroup.mk g₀ := hL _ ⟨Y, rfl⟩
  have hg₀x : ∀ x : Fin (2 + 2) ⊕ Fin (2 + 2) → K,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ K (g₀ : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) x =
        x + (x (.inr 0) + x (.inl 0)) • (Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1) +
          (x (.inr 1) + x (.inl 1)) • (Pi.single (.inl 1) 1 + Pi.single (.inr 1) 1) :=
    fun x => by
      rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hg₀, coe_oKappa, hY]
      exact oblk_oDSwap_mulVec x
  set e := statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
  set ĝ : matrixDerived (coordinateQuadPlus 4 K) :=
    statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) g₀
  have hc : e (QuotientGroup.mk' _ g₀) = matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ :=
    statedProjectiveReindexEquiv_mk (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) g₀
  set β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := e.symm.trans (β.trans e)
  have hβ' : β' (matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ) =
      matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ := by
    rw [← hc]
    exact congrArg e ((congrArg β (e.symm_apply_apply _)).trans hfix)
  set ρ := reindexVectorEquiv (K := K) (plusIndexEquiv 4)
  have hr : ∀ x, coordinateQuadPlus 4 K (ρ x) = quadPlus 4 K x :=
    reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  have hpol : ∀ (i : Fin 4) (x : Fin 4 ⊕ Fin 4 → K),
      polar (quadPlus 4 K) x (Pi.single (.inl i) 1 + Pi.single (.inr i) 1) =
        x (.inr i) + x (.inl i) := fun i x => by
    rw [polar_comm, polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_single_inl_quadPlus,
      CFSG.ClassicalGroups.Orthogonal.polar_single_inr_quadPlus]
  have hq1 : ∀ i : Fin 4, quadPlus 4 K (Pi.single (.inl i) 1 + Pi.single (.inr i) 1) = 1 :=
    fun i => by
      rw [quadPlus_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
  set u₀ : Fin 4 ⊕ Fin 4 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1
  set v₀ : Fin 4 ⊕ Fin 4 → K := Pi.single (.inl 1) 1 + Pi.single (.inr 1) 1
  have hu : coordinateQuadPlus 4 K (ρ u₀) = 1 := by rw [hr]; exact hq1 0
  have hv : coordinateQuadPlus 4 K (ρ v₀) = 1 := by rw [hr]; exact hq1 1
  have huv : polar (coordinateQuadPlus 4 K) (ρ u₀) (ρ v₀) = 0 := by
    rw [polar_map_isometry ρ hr, hpol]
    simp [u₀]
  have hlin : LinearIndependent K ![ρ u₀, ρ v₀] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h1 := congrFun hst (plusIndexEquiv 4 (.inl 0))
    have h2 := congrFun hst (plusIndexEquiv 4 (.inl 1))
    simp [ρ, reindexVectorEquiv_apply, u₀, v₀] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨g', -, hvec, -, -, -, hcent, -⟩ :=
    even_D4_rank_two_involution_full_centralizer_preserves_point_family _ hmod K hK
      (MulEquiv.refl _) hlin hu hv huv
  have hgg : ĝ = g' := by
    refine Subtype.ext (matrixLinearIso.injective (LinearEquiv.ext fun y => ?_))
    obtain ⟨x, rfl⟩ := ρ.surjective y
    have h1 : matrixLinearEquiv ĝ.val (ρ x) = ρ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin (2 + 2) ⊕ Fin (2 + 2)) K (g₀ : GL (Fin (2 + 2) ⊕ Fin (2 + 2)) K) x) :=
      statedDerivedReindexEquiv_vector (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) g₀ x
    have h2 := hvec (ρ x)
    rw [polar_map_isometry ρ hr, polar_map_isometry ρ hr, hpol, hpol] at h2
    change matrixLinearEquiv ĝ.val (ρ x) = matrixLinearEquiv g'.val (ρ x)
    rw [h1, h2, hg₀x x]
    simp only [map_add, map_smul]
  subst hgg
  have hcomm : β' * MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ) * β'⁻¹ =
      MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) ĝ) := by
    refine MulEquiv.ext fun z => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self, hβ']
  exact exists_semilinear_statedProj_of_mem (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
    β (hcent _ hcomm).2

end CFSG.ComponentClassification.RankTwoClassical
