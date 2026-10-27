module

public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG

namespace BaerSuzuki

theorem baer_suzuki_iff {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∀ g : G, IsPGroup p
        (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  constructor
  · intro hx g
    apply (Helpers.pCore_isPGroup (G := G) p).to_le
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hx
    · rw [Set.mem_singleton_iff] at hy
      subst y
      exact (Helpers.pCore_normal (G := G) p).conj_mem x hx g
  · intro h
    exact Helpers.mem_pCore_of_pairwise_conjugates x h

end BaerSuzuki

end CFSG
