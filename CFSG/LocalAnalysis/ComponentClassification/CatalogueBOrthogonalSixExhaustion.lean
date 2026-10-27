module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixExhaustionScalar
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixExhaustionReflection
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

@[expose] def sixGenerated (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    Subgroup (SixIsometries delta) :=
  (kappa delta h2).range ⊔ Subgroup.closure {sixGamma delta}

theorem six_kappa_mem_generated (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSimilitudes delta) :
    kappa delta h2 g ∈ sixGenerated delta h2 := by
  exact (le_sup_left : (kappa delta h2).range ≤ sixGenerated delta h2) ⟨g, rfl⟩

theorem six_gamma_mem_generated (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : sixGamma delta ∈ sixGenerated delta h2 := by
  exact (le_sup_right : Subgroup.closure {sixGamma delta} ≤ sixGenerated delta h2)
    (Subgroup.subset_closure (Set.mem_singleton (sixGamma delta)))

theorem six_reflection_mem_generated (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) [Invertible (sixForm delta X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (sixForm delta) X ∈
      sixGenerated delta h2 := by
  rw [six_reflection_eq_neg_anisotropic_gamma delta h2,
    ← sixGeneratorD_action delta h2]
  exact (sixGenerated delta h2).mul_mem (six_kappa_mem_generated delta h2 _)
    ((sixGenerated delta h2).mul_mem (six_kappa_mem_generated delta h2 _)
      (six_gamma_mem_generated delta h2))

theorem sixGenerated_eq_top (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : sixGenerated delta h2 = ⊤ := by
  let : NeZero (2 : K) := ⟨h2⟩
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let : FiniteDimensional K (sixSubmodule delta) :=
    Module.Finite.equiv (sixCoordinates delta h2)
  apply TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem (sixForm delta)
    (QuadraticMap.nondegenerate_polar_iff.mp (sixForm_nondegenerate delta h2))
  intro X _
  exact six_reflection_mem_generated delta h2 X

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
