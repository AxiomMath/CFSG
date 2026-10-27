module

public import Mathlib.GroupTheory.PGroup


public section

namespace CFSG.GroupTheory

theorem exists_odd_orderOf_preimage {G K : Type*} [Group G] [Finite G] [Group K]
    (f : G →* K) (hf : Function.Surjective f) {y : K} (hy : Odd (orderOf y)) :
    ∃ x : G, f x = y ∧ Odd (orderOf x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hf y
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hpow : (x₀ ^ 2 ^ e) ^ m = 1 := by
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  have hodd : Odd (orderOf (x₀ ^ 2 ^ e)) :=
    hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hcop : Nat.Coprime (2 ^ e) (orderOf y) :=
    (hy.coprime_two_right.pow_right e).symm
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := y) hcop
  refine ⟨(x₀ ^ 2 ^ e) ^ t, ?_, hodd.of_dvd_nat (orderOf_pow_dvd t)⟩
  rw [map_pow, map_pow, hx₀, ht]

theorem orderOf_map_eq_of_coprime_of_isPGroup_ker {G K : Type*} [Group G] [Group K] {p : ℕ}
    (f : G →* K) (hker : IsPGroup p f.ker) {x : G} (hx : (orderOf x).Coprime p) :
    orderOf (f x) = orderOf x := by
  have hdvd : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
  have hmem : x ^ orderOf (f x) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one (f x)
  obtain ⟨k, hk⟩ := hker.exists_orderOf_dvd_pow ⟨x ^ orderOf (f x), hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd' : orderOf (x ^ orderOf (f x)) ∣ orderOf x := orderOf_pow_dvd _
  have hone : orderOf (x ^ orderOf (f x)) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hx.pow_right k) hdvd' hk
  exact Nat.dvd_antisymm hdvd (orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.mp hone))

end CFSG.GroupTheory
