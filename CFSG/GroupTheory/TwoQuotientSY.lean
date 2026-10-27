module

public import CFSG.GroupTheory.QuasisimpleTwoQuotient

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {H : Type*} [Group H] [Finite H] {K S : Subgroup H}

theorem twoQuotientSY_pow_eq_one {n : ℕ}
    (h : ∀ s ∈ S, s ^ n ∈ Subgroup.centralizer (K : Set H))
    [hC : (twoQuotientC K S).Normal] :
    ∀ y ∈ twoQuotientSY K S hC, y ^ n = 1 := by
  intro y hy
  let J := K ⊔ S
  let C := twoQuotientC K S
  let π : ↥J →* twoQuotientY K S hC :=
    twoQuotientPi K S hC
  have hy' : y ∈ (S.subgroupOf J).map π := hy
  obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy'
  have hsS : ((s : ↥J) : H) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hpow : s ^ n ∈ C := by
    have h1 : s ^ n ∈ (S ⊓ Subgroup.centralizer (K : Set H)).subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp ((S.subgroupOf J).pow_mem hs n)
      · show (((s : ↥J) ^ n : ↥J) : H) ∈ Subgroup.centralizer (K : Set H)
        simpa using h (s : ↥J) hsS
    exact h1
  rw [← hsy]
  show (π s) ^ n = 1
  rw [← map_pow]
  have hπ : π (s ^ n) = (@QuotientGroup.mk' ↥J _ C hC) (s ^ n) := rfl
  rw [hπ, QuotientGroup.mk'_apply]
  exact (@QuotientGroup.eq_one_iff ↥J _ C hC (s ^ n)).mpr hpow

end CFSG.GroupTheory
