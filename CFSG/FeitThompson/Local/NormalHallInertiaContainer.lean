module

public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H U : Subgroup G} {A : Subgroup U}

theorem isPiSubgroup_centralizer_subgroupOf
    (hfree : ∀ q : ℕ, q.Prime → q ∉ π → ∀ v ∈ U, orderOf v = q →
      H ⊓ Subgroup.centralizer {v} = ⊥)
    {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) :
    IsPiSubgroup π ((Subgroup.centralizer {h}).subgroupOf U) := by
  refine isPiSubgroup_iff.2 fun q hq => ?_
  by_contra hqπ
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hord : orderOf ((v : U) : G) = q := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hv]
  have hcomm : ((v : U) : G) ∈ Subgroup.centralizer ({h} : Set G) :=
    Subgroup.mem_subgroupOf.1 v.2
  have hmem : h ∈ H ⊓ Subgroup.centralizer ({((v : U) : G)} : Set G) :=
    ⟨hh, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 hcomm).symm⟩
  rw [hfree q hqp hqπ _ (v : U).2 hord, Subgroup.mem_bot] at hmem
  exact hh1 hmem

theorem centralizer_subgroupOf_le_of_isHallPiSubgroup [A.Normal]
    (hA : IsHallPiSubgroup π A)
    (hfree : ∀ q : ℕ, q.Prime → q ∉ π → ∀ v ∈ U, orderOf v = q →
      H ⊓ Subgroup.centralizer {v} = ⊥)
    {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) :
    (Subgroup.centralizer {h}).subgroupOf U ≤ A :=
  hA.le_of_isPiSubgroup (isPiSubgroup_centralizer_subgroupOf hfree hh hh1)

theorem inf_centralizer_le_map_subtype_of_isHallPiSubgroup [A.Normal]
    (hA : IsHallPiSubgroup π A)
    (hfree : ∀ q : ℕ, q.Prime → q ∉ π → ∀ v ∈ U, orderOf v = q →
      H ⊓ Subgroup.centralizer {v} = ⊥)
    {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) :
    U ⊓ Subgroup.centralizer {h} ≤ A.map U.subtype := fun _ hx =>
  ⟨⟨_, hx.1⟩, centralizer_subgroupOf_le_of_isHallPiSubgroup hA hfree hh hh1
    (Subgroup.mem_subgroupOf.2 hx.2), rfl⟩

end

end CFSG.FeitThompson
