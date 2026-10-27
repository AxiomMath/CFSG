module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

theorem mem_closure_prime_powers_of_squarefree {G : Type*} [Group G] [Finite G] {x : G}
    (hx : Squarefree (orderOf x)) :
    x ∈ Subgroup.closure {y : G | y ∈ Subgroup.zpowers x ∧ (orderOf y).Prime} := by
  classical
  set n := orderOf x with hn
  let H : Subgroup G :=
    Subgroup.closure {y : G | y ∈ Subgroup.zpowers x ∧ (orderOf y).Prime}
  have hH_le : H ≤ Subgroup.zpowers x := by
    refine (Subgroup.closure_le (Subgroup.zpowers x)).mpr ?_
    rintro y ⟨hy, -⟩
    exact hy
  have hn0 : n ≠ 0 := by rw [hn]; exact (orderOf_pos x).ne'
  have hsq : Squarefree n := by rw [hn]; exact hx
  have hdvd : n ∣ Nat.card H := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Finset.prod_primes_dvd (Nat.card H) ?_ ?_
    · intro p hp
      exact (Nat.mem_primeFactors_of_ne_zero hn0).mp hp |>.1 |>.prime
    · intro p hp
      obtain ⟨hp_prime, hp_dvd⟩ := (Nat.mem_primeFactors_of_ne_zero hn0).mp hp
      have hord : orderOf (x ^ (n / p)) = p := orderOf_pow_orderOf_div hn0 hp_dvd
      have hmem : x ^ (n / p) ∈ H := by
        refine Subgroup.subset_closure ⟨?_, by rw [hord]; exact hp_prime⟩
        simpa using Subgroup.zpow_mem (Subgroup.mem_zpowers x) ((n / p : ℕ) : ℤ)
      have hle : Subgroup.zpowers (x ^ (n / p)) ≤ H := Subgroup.zpowers_le.mpr hmem
      rw [← hord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
  have hcard_le : Nat.card H ≤ n := by
    have hdvd' : Nat.card H ∣ n := by
      simpa [Nat.card_zpowers, hn] using Subgroup.card_dvd_of_le hH_le
    exact Nat.le_of_dvd (by rw [hn]; exact orderOf_pos x) hdvd'
  have hcard : Nat.card H = n :=
    le_antisymm hcard_le (Nat.le_of_dvd Nat.card_pos hdvd)
  have hHeq : H = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hH_le (by rw [hcard, Nat.card_zpowers, hn])
  change x ∈ H
  rw [hHeq]
  exact Subgroup.mem_zpowers x

theorem orderOf_squarefree_of_forall_sylow_square {G : Type*} [Group G] [Finite G]
    {C : Subgroup G} (hC : IsMulCommutative ↥C)
    (hP : ∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∃ P : Sylow p ↥C,
      Nat.card P = p ^ 2 ∧ ¬ IsCyclic ↥P)
    {c : G} (hc : c ∈ C) : Squarefree (orderOf c) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hp2
  have hpc : p ∣ Nat.card C :=
    (dvd_trans (dvd_mul_right p p) hp2).trans (Subgroup.orderOf_dvd_natCard C hc)
  obtain ⟨P, hPcard, hPnc⟩ := hP p hp hpc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥C := hC
  have hdiv : p ^ 2 ∣ orderOf (⟨c, hc⟩ : ↥C) := by
    simpa [pow_two, Subgroup.orderOf_mk] using hp2
  let y : ↥C := ⟨c, hc⟩ ^ (orderOf (⟨c, hc⟩ : ↥C) / p ^ 2)
  have hyord : orderOf y = p ^ 2 := orderOf_pow_orderOf_div (orderOf_pos _).ne' hdiv
  have hzcyc : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hyord])
  obtain ⟨Q, hQ⟩ := hzcyc.exists_le_sylow
  have hPn : (P : Subgroup ↥C).Normal := Subgroup.normal_of_comm (P : Subgroup ↥C)
  haveI huniq : Unique (Sylow p ↥C) := Sylow.unique_of_normal P hPn
  have hQP : Q = P := Subsingleton.elim Q P
  rw [hQP] at hQ
  have heq : Subgroup.zpowers y = (P : Subgroup ↥C) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [Nat.card_zpowers, hyord, hPcard])
  have hcycP : IsCyclic ↥(P : Subgroup ↥C) := by
    rw [← heq]
    exact Subgroup.isCyclic_zpowers y
  exact hPnc hcycP

end CFSG.GroupTheory

end
