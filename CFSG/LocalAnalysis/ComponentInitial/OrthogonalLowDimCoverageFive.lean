module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalFive

variable {K : Type*} [Field K]

theorem selfAdjointOrthogonalAction_mem_symplecticImage (h2 : (2 : K) ≠ 0)
    (A : symplecticSimilitudes K) {c : Kˣ} (hA : symplecticMultiplier A = c ^ 2) :
    selfAdjointOrthogonalAction h2 A ∈ selfAdjointSymplecticImage h2 := by
  have hker : A * selfAdjointScalarSimilitude c⁻¹ ∈ (symplecticMultiplier (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, hA, symplecticMultiplier_scalar, inv_pow, mul_inv_cancel]
  refine ⟨⟨_, hker⟩, ?_⟩
  change selfAdjointOrthogonalAction h2 (A * selfAdjointScalarSimilitude c⁻¹) = _
  rw [map_mul, selfAdjointOrthogonalAction_scalar, mul_one]

theorem selfAdjoint_sq_mem_symplecticImage (h2 : (2 : K) ≠ 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :
    g ^ 2 ∈ selfAdjointSymplecticImage h2 := by
  obtain ⟨⟨A, ε⟩, rfl⟩ := selfAdjointFullAction_surjective h2 g
  have hε : ε ^ 2 = 1 := Subtype.ext ((mem_rootsOfUnity 2 ε.val).mp ε.property)
  change (selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε) ^ 2 ∈ _
  rw [(selfAdjointScalarAction_commute h2 ε A).symm.mul_pow, ← map_pow, ← map_pow, hε, map_one,
    mul_one]
  exact selfAdjointOrthogonalAction_mem_symplecticImage h2 _ (c := symplecticMultiplier A)
    (map_pow _ _ _)

variable [Finite K]

theorem selfAdjointSymplecticImage_quasisimple (hodd : Odd (Nat.card K)) :
    CFSG.IsQuasisimple
      (selfAdjointSymplecticImage (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)) :=
  isQuasisimple_range_of_ker_le_center (symplecticKernel_quasisimple hodd) _
    (selfAdjointSymplecticAction_kernel_le_center _)

theorem selfAdjoint_commutator_eq (hodd : Odd (Nat.card K)) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) =
      selfAdjointSymplecticImage (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) :=
  commutator_eq_of_isPerfect_of_forall_sq_mem (selfAdjointSymplecticImage_quasisimple hodd).1
    (selfAdjoint_sq_mem_symplecticImage _)

end CFSG.LocalAnalysis.ComponentInitial
