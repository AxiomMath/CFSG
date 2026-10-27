module

public import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_comm_of_conj_mem_zpowers {g z : G} (hz : orderOf z = 3)
    (hgz : g * z * g⁻¹ ∈ zpowers z) (hg : Odd (orderOf g)) : g * z = z * g := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hgz
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨j, rfl⟩
    have h1 : z ^ ((3 : ℤ) * j) = 1 := by
      rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hz,
        pow_orderOf_eq_one, one_zpow]
    rw [h1] at hk
    have hz1 : z = 1 := by
      have := congrArg (fun t => g⁻¹ * t * g) hk
      simpa [mul_assoc] using this.symm
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hkk : k * k ≡ 1 [ZMOD 3] := by
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    unfold Int.ModEq
    rw [Int.mul_emod]
    rcases this with h | h <;> rw [h] <;> norm_num
  have h2 : g ^ 2 * z * (g ^ 2)⁻¹ = z := by
    calc g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = (z ^ k) ^ k := by rw [← hk, ← conj_zpow, ← hk]
      _ = z ^ (k * k) := by rw [← zpow_mul]
      _ = z ^ (1 : ℤ) := zpow_eq_zpow_iff_modEq.2 (by rw [hz]; exact_mod_cast hkk)
      _ = z := zpow_one z
  have hc : Commute (g ^ 2) z := by
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.2 hg)
  have := hc.pow_left m
  rw [hm] at this
  exact this.eq

theorem odd_orderOf_of_isPGroup_three {g : G} (hg : IsPGroup 3 (zpowers g)) :
    Odd (orderOf g) := by
  obtain ⟨k, hk⟩ := hg ⟨g, mem_zpowers g⟩
  have hdvd : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hk)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hb]
  exact Odd.pow (by decide)

theorem mem_zpowers_of_pow_three_eq_one {Q : Subgroup G} [Finite Q] (hQ : IsCyclic Q) {z u : G}
    (hz : orderOf z = 3) (hzQ : z ∈ Q) (huQ : u ∈ Q) (hu : u ^ 3 = 1) : u ∈ zpowers z := by
  have hle : zpowers (⟨u, huQ⟩ : Q) ≤ zpowers ⟨z, hzQ⟩ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz]
    exact orderOf_dvd_of_pow_eq_one hu
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hle (mem_zpowers _))
  exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem three_pow_dvd_three_mul_sub_one {b : ℕ} {m : ℤ} (h : (3 : ℤ) ^ b ∣ m ^ 3 - 1) :
    (3 : ℤ) ^ b ∣ 3 * (m - 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h3 : (3 : ℤ) ∣ m - 1 := by
    have h1 : (3 : ℤ) ∣ m ^ 3 - 1 := (dvd_pow_self 3 hb.ne').trans h
    have h2 : (3 : ℤ) ∣ (m - 1) ^ 3 := by
      have e : (m - 1) ^ 3 = (m ^ 3 - 1) - 3 * (m * (m - 1)) := by ring
      rw [e]
      exact dvd_sub h1 (dvd_mul_right 3 _)
    exact Int.prime_three.dvd_of_dvd_pow h2
  obtain ⟨t, ht⟩ := h3
  have hco : IsCoprime ((3 : ℤ) ^ b) (1 + 3 * (t + t ^ 2)) :=
    IsCoprime.pow_left ⟨-(t + t ^ 2), 1, by ring⟩
  have e : m ^ 3 - 1 = 3 * (m - 1) * (1 + 3 * (t + t ^ 2)) := by
    have hm : m = 1 + 3 * t := by omega
    subst hm
    ring
  rw [e] at h
  exact hco.dvd_of_dvd_mul_right h

theorem commutator_pow_three_of_isCyclic {Q : Subgroup G} (hQ : IsCyclic Q)
    (hQp : IsPGroup 3 Q) {y : G} (hyQ : y ∈ normalizer (Q : Set G)) (hy3 : y ^ 3 = 1)
    {c : G} (hc : c ∈ Q) : ⁅y, c⁆ ^ 3 = 1 := by
  have hconj : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.1 hyQ q).1 hq
  let σ : Q →* Q :=
    { toFun := fun q => ⟨y * q * y⁻¹, hconj q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hσ : ∀ q : Q, ((σ q : Q) : G) = y * q * y⁻¹ := fun _ => rfl
  obtain ⟨m, hm⟩ := σ.map_cyclic
  have hcm : y * c * y⁻¹ = c ^ m := by
    have := congrArg Subtype.val (hm ⟨c, hc⟩)
    rw [hσ] at this
    simpa using this
  have hcm3 : c ^ (m ^ 3) = c := by
    have e : ∀ n : ℕ, y ^ n * c * (y ^ n)⁻¹ = c ^ (m ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc y ^ (n + 1) * c * (y ^ (n + 1))⁻¹ = y * (y ^ n * c * (y ^ n)⁻¹) * y⁻¹ := by
              rw [pow_succ']; group
          _ = (y * c * y⁻¹) ^ (m ^ n) := by rw [ih, conj_zpow]
          _ = c ^ (m ^ (n + 1)) := by rw [hcm, ← zpow_mul, pow_succ', mul_comm]
    have := e 3
    rw [hy3] at this
    simpa using this.symm
  have hord : (orderOf c : ℤ) ∣ m ^ 3 - 1 := by
    rw [← Int.modEq_iff_dvd, Int.ModEq]
    have := (zpow_eq_zpow_iff_modEq (x := c)).1 (hcm3.trans (zpow_one c).symm)
    exact this.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, orderOf c = 3 ^ b := by
    obtain ⟨k, hk⟩ := hQp ⟨c, hc⟩
    have hdvd : orderOf c ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨b, hb⟩
  rw [hb] at hord
  have hd := three_pow_dvd_three_mul_sub_one (by exact_mod_cast hord)
  have hcomm : ⁅y, c⁆ = c ^ (m - 1) := by
    rw [commutatorElement_def, hcm, zpow_sub_one]
  rw [hcomm, ← zpow_natCast, ← zpow_mul]
  apply (orderOf_dvd_iff_zpow_eq_one).1
  rw [hb]
  simpa [mul_comm] using hd

theorem isPGroup_zpowers_of_pow_eq_one {p n : ℕ} {g : G} (hg : g ^ p ^ n = 1) :
    IsPGroup p (zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  refine ⟨n, Subtype.ext ?_⟩
  change (g ^ k) ^ p ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem pow_three_eq_one_of_mem_zpowers {z u : G} (hz : z ^ 3 = 1) (hu : u ∈ zpowers z) :
    u ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem mem_normalizer_of_pow_three {A : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (h : ∀ a ∈ A, x * a * x⁻¹ ∈ A) : x ∈ normalizer (A : Set G) := by
  refine mem_normalizer_iff.2 fun a => ⟨h a, fun ha => ?_⟩
  have e : a = x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ := by
    have : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * a * (x ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [this, hx3]
    group
  rw [e]
  exact h _ (h _ ha)

theorem zpowers_eq_of_forall_pow_three_ne {Q : Subgroup G} [Finite Q] (hQ : IsCyclic Q)
    (hQp : IsPGroup 3 Q) {c : G} (hc : c ∈ Q) (hnc : ∀ q ∈ Q, q ^ 3 ≠ c) : zpowers c = Q := by
  obtain ⟨⟨g, hgQ⟩, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hQg : ∀ q ∈ Q, q ∈ zpowers g := fun q hq => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨q, hq⟩)
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, g ^ n = c := by
    have h1 : (⟨c, hc⟩ : Q) ∈ Submonoid.powers (⟨g, hgQ⟩ : Q) :=
      mem_powers_iff_mem_zpowers.2 (hg _)
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have h3 : ¬ 3 ∣ n := by
    rintro ⟨t, rfl⟩
    exact hnc (g ^ t) (pow_mem hgQ t) (by rw [← pow_mul, mul_comm]; exact hn)
  obtain ⟨b, hb⟩ : ∃ b : ℕ, orderOf g = 3 ^ b := by
    obtain ⟨k, hk⟩ := hQp ⟨g, hgQ⟩
    have hdvd : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨b, hb⟩
  have hco : n.Coprime (orderOf g) := by
    rw [hb]
    exact Nat.Coprime.pow_right b
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
  have hgc : g ∈ zpowers c := by
    rw [← hm, hn]
    exact pow_mem (mem_zpowers c) m
  refine le_antisymm (zpowers_le.2 hc) fun q hq => ?_
  exact (zpowers_le.2 hgc) (hQg q hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
