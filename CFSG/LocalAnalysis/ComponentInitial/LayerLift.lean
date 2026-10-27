module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.LocalCores
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isComponent_commutator_of_surjective [Finite G] {H : Subgroup G} (hH : H.IsSubnormal)
    {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) (φ : H →* Q)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center H) : CFSG.IsComponent ⁅H, H⁆ := by
  have hHA : CFSG.IsQuasisimple (H ⧸ φ.ker) :=
    (isQuasisimple_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).2 hQ
  have hq : CFSG.IsQuasisimple (commutator H) := quasisimple_central_extension_derived hker hHA
  have hmap : (commutator H).map H.subtype = ⁅H, H⁆ := H.map_subtype_commutator
  refine ⟨(isQuasisimple_congr (((commutator H).equivMapOfInjective H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr hmap))).1 hq, ?_⟩
  rw [← hmap]
  exact (inferInstance : (_root_.commutator H).Normal).isSubnormal.trans' hH

end CFSG.LocalAnalysis.ComponentInitial
