module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

theorem exists_normal_complement_of_central_involution {G : Type*} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hzc : ∀ g : G, g * z = z * g) (hcard : (Nat.card G).factorization 2 = 1) :
    ∃ O : Subgroup G, O.Normal ∧ Odd (Nat.card O) ∧ ∀ g : G, g ∈ O ∨ g * z ∈ O := by
  have hZcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz]
  have hZp : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hcard]
    simp
  have hPeq : Subgroup.zpowers z = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hZP (by rw [hZcard, hPcard])
  have hP : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.zpowers z := by
      rw [hPeq]
      exact hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact (Commute.zpow_left (hzc g).symm k).eq
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨(MonoidHom.transferSylow P hP).ker, inferInstance, ?_, ?_⟩
  · exact Nat.not_even_iff_odd.mp fun h => MonoidHom.not_dvd_card_ker_transferSylow P hP h.two_dvd
  · intro g
    obtain ⟨⟨o, p⟩, hg⟩ := hcompl.2 g
    replace hg : (o : G) * p = g := hg
    subst hg
    have hp : (p : G) ∈ Subgroup.zpowers z := by
      rw [hPeq]
      exact p.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hz2 : z * z = 1 := by
      rw [← pow_two, ← hz]
      exact pow_orderOf_eq_one z
    have hk' : (p : G) = z ^ (k % 2) := by
      have := zpow_mod_orderOf z k
      rw [hz, Nat.cast_ofNat] at this
      rw [← hk, this]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [hk', h, zpow_zero, mul_one]
      exact o.2
    · right
      rw [hk', h, zpow_one, mul_assoc, hz2, mul_one]
      exact o.2

theorem exists_twoPart {G : Type*} [Group G] [Finite G] (w : G) :
    ∃ u v : G, u ∈ Subgroup.zpowers w ∧ v ∈ Subgroup.zpowers w ∧ w = u * v ∧
      (∃ j : ℕ, u ^ (2 ^ j) = 1) ∧ Odd (orderOf v) := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hcop : IsCoprime (b : ℤ) ((2 ^ a : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hb))
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨w ^ (s * b), w ^ (t * ((2 ^ a : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers w _,
    Subgroup.zpow_mem_zpowers w _, ?_, ⟨a, ?_⟩, ?_⟩
  · rw [← zpow_add, hst, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, mul_assoc, mul_comm (b : ℤ), ← Nat.cast_mul, ← hab]
    rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have hv : (w ^ (t * ((2 ^ a : ℕ) : ℤ))) ^ b = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_assoc, ← Nat.cast_mul, ← hab, mul_comm, zpow_mul,
        zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one hv)

theorem exists_conj_mem_sylow_of_pow {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {y : G}
    {j : ℕ} (hy : y ^ (2 ^ j) = 1) : ∃ g : G, g * y * g⁻¹ ∈ (S : Subgroup G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(zpowers y) := by
    have h2 : orderOf y ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hy
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨g, ?_⟩
  have hyQ : y ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨y, hyQ, by simp [MulAut.conj_apply]⟩

theorem involution_support_even {m : ℕ} {σ : Perm (Fin m)} (h : σ * σ = 1) :
    ∃ k : ℕ, σ.support.card = 2 * k := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, h]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  exact ⟨σ.cycleType.card, by rw [← hsum]; ring⟩

theorem factorization_two_eq_one_of_hall {G : Type*} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hall : ∀ g : G, (∃ j : ℕ, g ^ (2 ^ j) = 1) → g ∈ zpowers z) :
    (Nat.card G).factorization 2 = 1 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hZp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPZ : (P : Subgroup G) ≤ zpowers z := by
    intro g hg
    have hp : IsPGroup 2 ↥(P : Subgroup G) := P.isPGroup'
    obtain ⟨j, hj⟩ := hp ⟨g, hg⟩
    refine hall g ⟨j, ?_⟩
    have := congrArg (fun w : ↥(P : Subgroup G) => (w : G)) hj
    simpa using this
  have hPcard : Nat.card P = 2 := by
    have h1 : Nat.card (zpowers z) ≤ Nat.card (P : Subgroup G) := Subgroup.card_le_of_le hZP
    have h2 : Nat.card (P : Subgroup G) ≤ Nat.card (zpowers z) := Subgroup.card_le_of_le hPZ
    omega
  rw [P.card_eq_multiplicity] at hPcard
  have : 2 ^ (Nat.card G).factorization 2 = 2 ^ 1 := by simpa using hPcard
  exact Nat.pow_right_injective (le_refl 2) this

end CFSG.OddStandard.Solomon75
