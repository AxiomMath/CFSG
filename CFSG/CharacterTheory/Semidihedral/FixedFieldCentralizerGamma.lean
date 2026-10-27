module

public import CFSG.CharacterTheory.Semidihedral.OddFieldLift

public section

namespace CFSG.Semidihedral.FixedFieldCentralizerGamma

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.OddFieldLift

universe u

theorem linearInclusion_mem_Gamma (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (d : coordinateD F) : linearInclusion F d ∈ Gamma F A :=
  Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 (by rw [linearInclusion_coe]; exact d.property))

end CFSG.Semidihedral.FixedFieldCentralizerGamma
