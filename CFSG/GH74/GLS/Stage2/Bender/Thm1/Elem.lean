module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der65

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Invol

variable {G : Type} [Group G]

theorem conj_conj_of_mul_self {z : G} (hz : z * z = 1) (x : G) : z * (z * x * z⁻¹) * z⁻¹ = x := by
  calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
    _ = x := by rw [hz]; simp

theorem conj_inv_elt {z : G} (hz : z * z = 1) (r : G) :
    z * (r⁻¹ * (z * r * z⁻¹)) * z⁻¹ = (r⁻¹ * (z * r * z⁻¹))⁻¹ := by
  have hs := conj_conj_of_mul_self hz r
  calc z * (r⁻¹ * (z * r * z⁻¹)) * z⁻¹
      = (z * r * z⁻¹)⁻¹ * (z * (z * r * z⁻¹) * z⁻¹) := by group
    _ = (z * r * z⁻¹)⁻¹ * r := by rw [hs]
    _ = (r⁻¹ * (z * r * z⁻¹))⁻¹ := by group

theorem inverts_zpowers {z a : G} (h : z * a * z⁻¹ = a⁻¹) : Inverts z (zpowers a) := by
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, inv_zpow]

theorem inv_conj_inv {z a : G} (h : z * a * z⁻¹ = a⁻¹) : z⁻¹ * a * z⁻¹⁻¹ = a⁻¹ := by
  have h2 : a = z * a⁻¹ * z⁻¹ := by
    calc a = (a⁻¹)⁻¹ := (inv_inv a).symm
      _ = (z * a * z⁻¹)⁻¹ := by rw [h]
      _ = z * a⁻¹ * z⁻¹ := by group
  calc z⁻¹ * a * z⁻¹⁻¹ = z⁻¹ * (z * a⁻¹ * z⁻¹) * z := by rw [← h2, inv_inv]
    _ = a⁻¹ := by group

theorem mem_normalizer_zpowers_of_inv {z a : G} (h : z * a * z⁻¹ = a⁻¹) :
    z ∈ normalizer ((zpowers a : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [inverts_zpowers h y hy]
    exact (Subgroup.inv_mem_iff _).mpr hy
  · intro hy
    have h' := inverts_zpowers (inv_conj_inv h) (z * y * z⁻¹) hy
    have h2 : z⁻¹ * (z * y * z⁻¹) * z⁻¹⁻¹ = y := by group
    rw [h2] at h'
    rw [h']
    exact (Subgroup.inv_mem_iff _).mpr hy

theorem mem_zpowers_cases {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) : g = 1 ∨ g = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  have hn : z ^ n = z ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul, hz2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [hn, h, zpow_zero]
  · right
    rw [hn, h, zpow_one]

theorem exists_inverted {z : G} (hz : z * z = 1) {A : Subgroup G}
    (hzA : z ∈ normalizer (A : Set G)) (hA : ¬ A ≤ Cen z) : ∃ a ∈ A, a ≠ 1 ∧ z * a * z⁻¹ = a⁻¹ := by
  rw [IsConcreteLE.not_le_iff_exists] at hA
  obtain ⟨r, hrA, hrz⟩ := hA
  have hrz' : ¬ (z * r * z⁻¹ = r) := by
    intro h
    apply hrz
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * z = z * r * z⁻¹ * z := by rw [h]
      _ = z * r := by group
  refine ⟨r⁻¹ * (z * r * z⁻¹), A.mul_mem (A.inv_mem hrA) ((mem_normalizer_iff.mp hzA r).mp hrA), ?_,
    conj_inv_elt hz r⟩
  intro h
  apply hrz'
  calc z * r * z⁻¹ = r * (r⁻¹ * (z * r * z⁻¹)) := by group
    _ = r := by rw [h, mul_one]

theorem exists_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha : a ^ p = 1) :
    ∃ m : ℕ, (a ^ 2) ^ m = a := by
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  rw [← pow_mul]
  calc a ^ (2 * (k + 1)) = a ^ (2 * k + 1 + 1) := by rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    _ = a ^ (2 * k + 1) * a := pow_succ _ _
    _ = a := by rw [← hk, ha, one_mul]

theorem exists_sqrt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha : a ^ p = 1) :
    ∃ s ∈ zpowers a, s ^ 2 = a := by
  obtain ⟨m, hm⟩ := exists_two_pow hp hp2 ha
  refine ⟨a ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul]
  exact hm

theorem commutator_zpowers_eq_of_inverts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z a : G}
    (ha : a ^ p = 1) (h : z * a * z⁻¹ = a⁻¹) : ⁅zpowers a, zpowers z⁆ = zpowers a := by
  apply le_antisymm
  · exact commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_inv h))
  · rw [Subgroup.zpowers_le]
    obtain ⟨m, hm⟩ := exists_two_pow hp hp2 ha
    have hcomm : ⁅a, z⁆ = a ^ 2 := by
      have : z * a⁻¹ * z⁻¹ = a := by
        calc z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
          _ = a := by rw [h, inv_inv]
      calc ⁅a, z⁆ = a * (z * a⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
        _ = a ^ 2 := by rw [this, pow_two]
    have h1 : a ^ 2 ∈ ⁅zpowers a, zpowers z⁆ := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers z)
    have h2 := Subgroup.pow_mem _ h1 m
    rwa [hm] at h2

theorem mul_self_eq_one_of_orderOf_two {z : G} (hz : orderOf z = 2) : z * z = 1 := by
  rw [← pow_two, ← hz]
  exact pow_orderOf_eq_one z

theorem commutator_zpowers_eq_bot_iff {z : G} {A : Subgroup G} :
    ⁅A, zpowers z⁆ = ⊥ ↔ A ≤ Cen z := by
  constructor
  · intro h
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)))
  · intro h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute a z := Subgroup.mem_centralizer_singleton_iff.mp (h ha)
    exact ((hc.zpow_right n).eq).symm

end Invol

section Fin

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ normalizer (H : Set G) :=
  Subgroup.mem_normalizer_fintype h

theorem le_normalizer_of_commutes {H K : Subgroup G} (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ≤ normalizer (K : Set G) := fun x hx =>
  mem_normalizer_of_forall fun y hy => by
    have : x * y * x⁻¹ = y := by rw [h x hx y hy]; group
    rw [this]
    exact hy

theorem prime_le_card_of_ne_bot {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : IsPGroup p ↥X)
    (h0 : X ≠ ⊥) : p ≤ Nat.card ↥X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hX
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h0 (Subgroup.eq_bot_of_card_eq X (by rw [hn, pow_zero]))
  rw [hn]
  exact Nat.le_self_pow hn0 p

omit [Finite G] in
theorem ne_inv_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} (ha1 : a ≠ 1) (hap : a ^ p = 1) :
    a ≠ a⁻¹ := by
  intro h
  have h2 : a ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h
  have hd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hdp : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h1 : orderOf a ∣ Nat.gcd 2 p := Nat.dvd_gcd hd2 hdp
  rw [hcop.gcd_eq_one] at h1
  exact ha1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

theorem mem_normalizer_zpowers_of_comm {z v : G} (h : z * v = v * z) :
    z ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have : z * v ^ n * z⁻¹ = v ^ n := by
    have hc : Commute z v := h
    rw [(hc.zpow_right n).eq]
    group
  rw [this]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) n

end Fin

end CFSG.GH74.GLS.Stage2.Bender.Thm1
