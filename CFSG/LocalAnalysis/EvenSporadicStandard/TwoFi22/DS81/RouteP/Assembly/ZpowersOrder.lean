module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem eq_one_of_mem_zpowers_of_pow_eq_one {G : Type*} [Group G] {t x : G} {n : ℕ}
    (hn : Nat.Coprime (orderOf t) n) (hx : x ∈ Subgroup.zpowers t) (hxn : x ^ n = 1) :
    x = 1 := by
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hn (orderOf_dvd_of_mem_zpowers hx)
    (orderOf_dvd_of_pow_eq_one hxn)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
