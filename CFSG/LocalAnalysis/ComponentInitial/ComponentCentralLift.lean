module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

noncomputable def comapMkQuotientEquiv (Z : Subgroup G) [Z.Normal] (L : Subgroup (G ⧸ Z)) :
    (L.comap (QuotientGroup.mk' Z)) ⧸ Z.subgroupOf (L.comap (QuotientGroup.mk' Z)) ≃* L := by
  set H := L.comap (QuotientGroup.mk' Z)
  let φ : H →* L := ((QuotientGroup.mk' Z).comp H.subtype).codRestrict L fun h => h.2
  have hφ : Function.Surjective φ := by
    rintro ⟨l, hl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z l
    exact ⟨⟨g, hl⟩, rfl⟩
  have hker : Z.subgroupOf H = φ.ker := by
    ext h
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hz
      exact Subtype.ext ((QuotientGroup.eq_one_iff (h : G)).2 hz)
    · intro h1
      exact (QuotientGroup.eq_one_iff (h : G)).1 (congrArg Subtype.val h1)
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end CFSG.LocalAnalysis.ComponentInitial
