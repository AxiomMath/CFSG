module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem reindexMatrixEquiv_glAut (eI : ι ≃ Fin d) (σ : K ≃+* K) (g : GL ι K) :
    reindexMatrixEquiv eI (glAut σ g) =
      CatalogueBHigherLinearField.glFieldAut (Fin d) K σ (reindexMatrixEquiv eI g) := by
  apply Units.ext
  ext i j
  rfl

theorem exists_semilinear_statedProj (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (htop : matrixProjectiveImage (reindexQuadraticForm eI Q) = ⊤)
    (β : MulAut (StatedProj (StatedOmega Q₀))) :
    ∃ (σ : K ≃+* K) (A : GL ι K) (μ : K), μ ≠ 0 ∧
      (∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q₀ v)) ∧
      ∀ g : StatedOmega Q₀, ∃ hg : A * glAut σ (g : GL ι K) * A⁻¹ ∈ StatedOmega Q₀,
        β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
  obtain ⟨s, hsβ⟩ := (mem_matrixProjectiveImage_iff (reindexQuadraticForm eI Q)
    (((statedProjectiveReindexEquiv eI Q hQ).symm.trans
      (β.trans (statedProjectiveReindexEquiv eI Q hQ))))).mp
    (by rw [htop]; exact Subgroup.mem_top _)
  obtain ⟨μ, hμ⟩ := s.2
  set A : GL ι K := (reindexMatrixEquiv eI).symm s.val.left with hA
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

variable [Finite K]

theorem exists_semilinear_plus {n : ℕ} (hn : 5 ≤ n)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin n ⊕ Fin n) K) (μ : K), μ ≠ 0 ∧
      (∀ v, StatedQuadPlus n K ((A : Matrix _ _ K) *ᵥ fun i => σ (v i)) =
        μ * σ (StatedQuadPlus n K v)) ∧
      ∀ g : StatedOmega (StatedQuadPlus n K),
        ∃ hg : A * glAut σ (g : GL (Fin n ⊕ Fin n) K) * A⁻¹ ∈ StatedOmega (StatedQuadPlus n K),
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ :=
  exists_semilinear_statedProj (plusIndexEquiv n) (CFSG.LieType.Universal.Spin.quadPlus n K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn) β

theorem exists_semilinear_minus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :
    ∃ (σ : K ≃+* K) (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) (μ : K), μ ≠ 0 ∧
      (∀ v, StatedQuadMinus n K b c ((A : Matrix _ _ K) *ᵥ fun i => σ (v i)) =
        μ * σ (StatedQuadMinus n K b c v)) ∧
      ∀ g : StatedOmega (StatedQuadMinus n K b c),
        ∃ hg : A * glAut σ (g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) * A⁻¹ ∈
          StatedOmega (StatedQuadMinus n K b c),
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ :=
  exists_semilinear_statedProj (minusIndexEquiv n (by omega))
    (CFSG.LieType.Universal.Spin.quadMinus n K b c)
    (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr) β

end CFSG.ComponentClassification.RankTwoClassical
