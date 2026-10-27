module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem r1s_dvd_sub_one {c : ℤ} {b k : ℕ} (hc : (3 : ℤ) ∣ c - 1) (hb : ¬ 3 ∣ b)
    (h : (3 : ℤ) ^ k ∣ c ^ b - 1) : (3 : ℤ) ^ k ∣ c - 1 := by
  have hq : ¬ (3 : ℤ) ∣ ∑ i ∈ Finset.range b, c ^ i := by
    intro h3
    apply hb
    have h1 : ((∑ i ∈ Finset.range b, c ^ i : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
    have hc' : (c : ZMod 3) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (c - 1) 3).mpr hc
      simpa [sub_eq_zero] using this
    push_cast at h1
    simp [hc'] at h1
    exact (ZMod.natCast_eq_zero_iff b 3).mp h1
  have hcop : IsCoprime ((3 : ℤ) ^ k) (∑ i ∈ Finset.range b, c ^ i) :=
    IsCoprime.pow_left (Int.prime_three.coprime_iff_not_dvd.mpr hq)
  have hmul : (∑ i ∈ Finset.range b, c ^ i) * (c - 1) = c ^ b - 1 := geom_sum_mul c b
  rw [← hmul, mul_comm] at h
  exact hcop.dvd_of_dvd_mul_right h

theorem r1s_commute_of_pow_mem {H : Type*} [Group H] {S : Subgroup H} [hS : IsCyclic S]
    {k : ℕ} (hk : Nat.card S = 3 ^ k) {z n : H} (hzS : z ∈ S) (hzo : orderOf z = 3)
    (hn : n ∈ normalizer (S : Set H)) (hnz : n * z = z * n) {b : ℕ} (hb : ¬ 3 ∣ b)
    (hbS : n ^ b ∈ S) : ∀ s ∈ S, n * s = s * n := by
  obtain ⟨g, hg⟩ := hS.exists_generator
  set s : H := (g : H) with hsdef
  have hsord : orderOf s = 3 ^ k := by
    rw [hsdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hSz : ∀ y ∈ S, ∃ m : ℤ, s ^ m = y := by
    intro y hy
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hs : s ∈ S := g.2
  obtain ⟨c, hc⟩ := hSz (n * s * n⁻¹) ((mem_normalizer_iff.mp hn s).mp hs)
  have hiter : ∀ j : ℕ, n ^ j * s * (n ^ j)⁻¹ = s ^ (c ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n ^ (j + 1) * s * (n ^ (j + 1))⁻¹ = n * (n ^ j * s * (n ^ j)⁻¹) * n⁻¹ := by group
        _ = n * s ^ (c ^ j) * n⁻¹ := by rw [ih]
        _ = (n * s * n⁻¹) ^ (c ^ j) := by rw [conj_zpow]
        _ = (s ^ c) ^ (c ^ j) := by rw [hc]
        _ = s ^ (c ^ (j + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  obtain ⟨m0, hm0⟩ := hSz (n ^ b) hbS
  have hcomm : n ^ b * s * (n ^ b)⁻¹ = s := by
    rw [← hm0]
    have := (Commute.self_zpow s m0).eq
    calc s ^ m0 * s * (s ^ m0)⁻¹ = (s ^ m0 * s) * (s ^ m0)⁻¹ := rfl
      _ = (s * s ^ m0) * (s ^ m0)⁻¹ := by rw [this]
      _ = s := by group
  have h1 : (3 : ℤ) ^ k ∣ c ^ b - 1 := by
    have h2 : s ^ (c ^ b - 1) = 1 := by
      rw [zpow_sub_one, ← hiter b, hcomm, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hsord, Nat.cast_pow, Nat.cast_ofNat] at this
  obtain ⟨m, hm⟩ := hSz z hzS
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have hnotdvd : ¬ (3 : ℤ) ^ k ∣ m := by
    intro h
    apply hz1
    rw [← hm]
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hsord, Nat.cast_pow, Nat.cast_ofNat])
  have h3m : (3 : ℤ) ^ k ∣ m * 3 := by
    have h2 : s ^ (m * 3) = 1 := by
      rw [zpow_mul, hm]
      have := pow_orderOf_eq_one z
      rw [hzo] at this
      simpa using this
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hsord, Nat.cast_pow, Nat.cast_ofNat] at this
  have hcz : (3 : ℤ) ^ k ∣ m * (c - 1) := by
    have h2 : s ^ (m * (c - 1)) = 1 := by
      have hnz' : n * s ^ m * n⁻¹ = s ^ m := by
        rw [hm]
        calc n * z * n⁻¹ = z * n * n⁻¹ := by rw [hnz]
          _ = z := by group
      have h3 : n * s ^ m * n⁻¹ = s ^ (c * m) := by
        rw [← conj_zpow, ← hc, ← zpow_mul]
      rw [h3] at hnz'
      rw [mul_sub, mul_one, zpow_sub, ← hnz', mul_comm c m, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hsord, Nat.cast_pow, Nat.cast_ofNat] at this
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with _ | k'
    · exact absurd (by simp) hnotdvd
    · exact ⟨k', rfl⟩
  have h3m' : (3 : ℤ) ^ k' ∣ m := by
    have : (3 : ℤ) * 3 ^ k' ∣ 3 * m := by
      have := h3m
      rw [pow_succ, mul_comm] at this
      rwa [mul_comm m 3] at this
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  obtain ⟨m', rfl⟩ := h3m'
  have hm'3 : ¬ (3 : ℤ) ∣ m' := by
    intro h
    obtain ⟨t, rfl⟩ := h
    apply hnotdvd
    exact ⟨t, by ring⟩
  have h3c : (3 : ℤ) ∣ c - 1 := by
    have : (3 : ℤ) ^ k' * 3 ∣ 3 ^ k' * (m' * (c - 1)) := by
      rw [← pow_succ]
      have := hcz
      rwa [mul_assoc] at this
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero k' (by norm_num : (3 : ℤ) ≠ 0))).mp this
    rcases Int.prime_three.dvd_or_dvd h4 with h | h
    · exact absurd h hm'3
    · exact h
  have h5 := r1s_dvd_sub_one h3c hb h1
  have h6 : s ^ (c - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rwa [hsord, Nat.cast_pow, Nat.cast_ofNat]
  have h7 : n * s * n⁻¹ = s := by
    rw [← hc]
    have : s ^ c = s ^ (c - 1) * s := by rw [← zpow_add_one]; simp
    rw [this, h6, one_mul]
  have h8 : n * s = s * n := by
    calc n * s = (n * s * n⁻¹) * n := by group
      _ = s * n := by rw [h7]
  intro y hy
  obtain ⟨j, rfl⟩ := hSz y hy
  exact (Commute.zpow_right (h8 : Commute n s) j).eq

theorem r1s_normalizer_le_centralizer {H : Type*} [Group H] [Finite H] (S : Sylow 3 H)
    (hcyc : IsCyclic ↥(S : Subgroup H)) {z : H} (hz : z ∈ center H) (hzo : orderOf z = 3) :
    normalizer ((S : Subgroup H) : Set H) ≤ centralizer ((S : Subgroup H) : Set H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzS : z ∈ (S : Subgroup H) := by
    have : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hz)
    have hp : IsPGroup 3 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
    exact hp.le_sylow_of_normal S (mem_zpowers z)
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  intro n hn
  set N : Subgroup H := normalizer ((S : Subgroup H) : Set H) with hN
  have hSN : (S : Subgroup H) ≤ N := le_normalizer
  have hb : ¬ 3 ∣ (S : Subgroup H).relIndex N :=
    fun h => S.not_dvd_index (h.trans (relIndex_dvd_index_of_le hSN))
  have hbS : n ^ (S : Subgroup H).relIndex N ∈ (S : Subgroup H) :=
    pow_index_mem ((S : Subgroup H).subgroupOf N) (⟨n, hn⟩ : N)
  have hcomm := r1s_commute_of_pow_mem (S := (S : Subgroup H)) (hS := hcyc) hk hzS hzo hn
    (mem_center_iff.mp hz n) hb hbS
  exact fun s hs => (hcomm s hs).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
