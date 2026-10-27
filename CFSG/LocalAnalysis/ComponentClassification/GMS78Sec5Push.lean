module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T R R₂ U : Subgroup G} {a : ℕ} {y d : G}

namespace SzR

variable (hS : SzR G L T R a y d)
include hS

theorem normalizer_le_normalizer_gmsA
    (hR₂ : IsR₂ L T R R₂ d) : normalizer (R : Set G) ≤ normalizer (gmsA L T : Set G) := by
  intro h hh
  refine mem_normalizer_of_conj_mem_of_finite fun b hb => ?_
  refine hS.mem_gmsA_of_forall_commute hR₂
    ((mem_normalizer_iff.mp hh b).mp (hR₂.le_R (hR₂.gmsA_le hb))) fun r hr => ?_
  have hr' : h⁻¹ * r * h ∈ R := by
    have := (mem_normalizer_iff.mp (inv_mem hh) r).mp hr
    simpa using this
  have hc := hS.commute_gmsA hr' hb
  calc r * (h * b * h⁻¹) = h * (h⁻¹ * r * h * b) * h⁻¹ := by group
    _ = h * (b * (h⁻¹ * r * h)) * h⁻¹ := by rw [hc]
    _ = h * b * h⁻¹ * r := by group

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
