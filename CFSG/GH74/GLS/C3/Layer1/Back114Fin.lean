module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.GH74.GLS

private theorem even_involution_cycleType {n : ℕ} (hn : n ≤ 7) {u : Equiv.Perm (Fin n)} (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (hsign : Equiv.Perm.sign u = 1) : u.cycleType = {2, 2} := by
  have hord : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have hall : ∀ m ∈ u.cycleType, m = 2 := by
    intro m hm
    have h1 : m ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hm).trans hord
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hm
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  obtain ⟨k, hrep⟩ : ∃ k, u.cycleType = Multiset.replicate k 2 :=
    ⟨_, Multiset.eq_replicate_of_mem hall⟩
  have hsum : u.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate]
    simp [mul_comm]
  have hcard : Multiset.card u.cycleType = k := by rw [hrep, Multiset.card_replicate]
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hu1
    rw [← Equiv.Perm.cycleType_eq_zero]
    rw [hrep]
    rfl
  have hkeven : Even k := by
    by_contra hke
    rw [Nat.not_even_iff_odd] at hke
    rw [Equiv.Perm.sign_of_cycleType, hsum, hcard] at hsign
    have : Odd (2 * k + k) := by
      obtain ⟨m, hm⟩ := hke
      exact ⟨3 * m + 1, by omega⟩
    rw [Odd.neg_one_pow this] at hsign
    exact absurd hsign (by decide)
  have hkle : 2 * k ≤ 7 := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    calc u.support.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
      _ ≤ 7 := hn
  obtain ⟨m, hm⟩ := hkeven
  have hk2 : k = 2 := by omega
  rw [hrep, hk2]
  rfl

private theorem card_centralizer_two_two {n : ℕ} {σ : Equiv.Perm (Fin n)} (hct : σ.cycleType = {2, 2}) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) = Nat.factorial (n - 4) * 8 := by
  rw [Equiv.Perm.nat_card_centralizer, hct, Fintype.card_fin]
  have h1 : ({2, 2} : Multiset ℕ).sum = 4 := by simp
  have h2 : ({2, 2} : Multiset ℕ).prod = 4 := by simp
  have h3 : ∏ m ∈ ({2, 2} : Multiset ℕ).toFinset, Nat.factorial (({2, 2} : Multiset ℕ).count m) = 2 := by
    decide
  rw [h1, h2, h3]
  ring

private theorem eq_one_of_commute_of_coprime {n d : ℕ} {σ π : Equiv.Perm (Fin n)} (hc : π * σ = σ * π)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))) d)
    (hπ : π ^ d = 1) : π = 1 := by
  have hmem : π ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.mem_centralizer_singleton_iff.2 hc
  let π' : ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) := ⟨π, hmem⟩
  have h1 : orderOf π' ∣ Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) :=
    orderOf_dvd_natCard π'
  have h2 : orderOf π' ∣ d := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [π'] using hπ))
  have h3 : orderOf π' ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  have h4 : π' = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact congrArg Subtype.val h4

theorem no_odd_commuting_five : ∀ σ π : Equiv.Perm (Fin 5), σ ^ 2 = 1 → σ ≠ 1 →
    Equiv.Perm.sign σ = 1 → π * σ = σ * π → π ^ 15 = 1 → π = 1 := by
  intro σ π hσ2 hσ1 hs hc hπ
  have hcard := card_centralizer_two_two (even_involution_cycleType (by norm_num) hσ2 hσ1 hs)
  exact eq_one_of_commute_of_coprime hc (by rw [hcard]; decide) hπ

theorem no_odd_commuting_six : ∀ σ π : Equiv.Perm (Fin 6), σ ^ 2 = 1 → σ ≠ 1 →
    Equiv.Perm.sign σ = 1 → π * σ = σ * π → π ^ 45 = 1 → π = 1 := by
  intro σ π hσ2 hσ1 hs hc hπ
  have hcard := card_centralizer_two_two (even_involution_cycleType (by norm_num) hσ2 hσ1 hs)
  exact eq_one_of_commute_of_coprime hc (by rw [hcard]; decide) hπ

theorem dvd_of_odd_of_dvd_mul_two_pow {d m k : ℕ} (hodd : Odd d) (hd : d ∣ m * 2 ^ k) : d ∣ m :=
  Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)) hd

end CFSG.GH74.GLS
