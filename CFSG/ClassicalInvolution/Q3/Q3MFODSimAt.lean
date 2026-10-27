module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Out
public import CFSG.ClassicalInvolution.Q3.Q3TJD4Fam
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3TIRed
public import CFSG.ClassicalInvolution.Q3.Q3TJOrth
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.Q3.Q3T
open scoped Pointwise

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem spin_aut_similarity_at (Q : QuadraticForm F (ι → F)) {Q₀ : (ι → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀) [Group.IsPerfect (spinGroup Q)]
    (α : spinGroup Q ≃* spinGroup Q) (β : MulAut (StatedProj (StatedOmega Q₀)))
    (hβ : ∀ x, β (spinToStatedProj Q hR x) = spinToStatedProj Q hR (α x))
    (hsim : ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
        ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
          (y : GL ι F) = A * glFieldEquiv ι φ (x : GL ι F) * A⁻¹ ∧
            β (QuotientGroup.mk x) = QuotientGroup.mk y) :
    ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
      ∀ x, spinMatrix Q (α x) = A * glFieldEquiv ι φ (spinMatrix Q x) * A⁻¹ := by
  obtain ⟨A, φ, μ, hQ, hA⟩ := hsim
  refine ⟨A, φ, μ, hQ, fun x => ?_⟩
  let M : spinGroup Q →* GL ι F := (MulAut.conj A).toMonoidHom.comp
    ((glFieldEquiv ι φ).toMonoidHom.comp (spinMatrix Q))
  have hN : (spinMatrix Q).comp α.toMonoidHom = M := by
    refine eq_of_inv_mul_mem_center M _ fun x => ?_
    obtain ⟨y, hy, hβy⟩ := hA ⟨spinMatrix Q x, spinMatrix_mem_of_range_eq Q hR x⟩
    have h1 := hβ x
    rw [spinToStatedProj_apply, spinToStatedProj_apply] at h1
    rw [h1] at hβy
    have h2 := QuotientGroup.eq.mp hβy
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : (((⟨spinMatrix Q (α x), spinMatrix_mem_of_range_eq Q hR (α x)⟩ :
        StatedOmega Q₀)⁻¹ * y : StatedOmega Q₀) : GL ι F) =
        (spinMatrix Q (α x))⁻¹ * M x := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy]
      rfl
    rw [h3] at h2
    show (spinMatrix Q (α x))⁻¹ * M x ∈ Subgroup.center (GL ι F)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact h2
  exact DFunLike.congr_fun hN x

end Generic

section Plus4

local notation "𝔽₃" => GaloisField 3 1

theorem exists_similarity_plus4_of_family
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 𝔽₃))))
    (hβ : β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃)) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) 𝔽₃) (φ : 𝔽₃ ≃+* 𝔽₃) (μ : 𝔽₃ˣ),
      (∀ v, quadPlus 4 𝔽₃ (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus 4 𝔽₃ v)) ∧
      ∀ x : StatedOmega (StatedQuadPlus 4 𝔽₃), ∃ y : StatedOmega (StatedQuadPlus 4 𝔽₃),
        (y : GL (Fin 4 ⊕ Fin 4) 𝔽₃) = A * glFieldEquiv _ φ (x : GL _ 𝔽₃) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have hK : Nat.card 𝔽₃ = 3 ^ 1 := by rw [ModelFacts.TG3.natCard_galoisField_three, pow_one]
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 𝔽₃)))
      .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, 𝔽₃, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hγ : MulAut.congr (plusCoordinateEquiv 4 𝔽₃) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 𝔽₃) := by
    rw [← coordinate_plus_family_eq_matrixImage hT _ hK (MulEquiv.refl _),
      mem_projectivePointFamilyAut_iff]
    have key := familyTransport_automorphism (plusCoordinateEquiv 4 𝔽₃)
      (statedPointFamily (coe_quadPlus 4 𝔽₃)) β
    rw [hβ, plusCoordinate_pointFamily] at key
    exact key.symm
  exact ModelFacts.OrthAut.exists_similarity_of_mem_image (plusIndexEquiv 4) (quadPlus 4 𝔽₃)
    (coe_quadPlus 4 𝔽₃) β hγ

theorem spin_plus4_sim_of_family [Group.IsPerfect (spinGroup (quadPlus 4 𝔽₃))]
    (α : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃))
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 𝔽₃))))
    (hβ : ∀ x, β (d4Proj 𝔽₃ x) = d4Proj 𝔽₃ (α x))
    (hF : β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃)) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) 𝔽₃) (φ : 𝔽₃ ≃+* 𝔽₃) (μ : 𝔽₃ˣ),
      (∀ v, quadPlus 4 𝔽₃ (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus 4 𝔽₃ v)) ∧
      ∀ x, spinMatrix (quadPlus 4 𝔽₃) (α x) =
        A * glFieldEquiv _ φ (spinMatrix (quadPlus 4 𝔽₃) x) * A⁻¹ :=
  spin_aut_similarity_at (quadPlus 4 𝔽₃) (range_spinMatrix_quadPlus three_le_four) α β hβ
    (exists_similarity_plus4_of_family β hF)

end Plus4

end CFSG.ClassicalInvolution.Q3.Q3MFOD
