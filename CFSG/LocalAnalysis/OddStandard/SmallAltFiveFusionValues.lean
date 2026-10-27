module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveQForm

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G] {P S : Subgroup G} {s x : G} {a : ℕ}

theorem odd_mul_self_modEq_one_cases {l : ℕ} (ha : 2 ≤ a) (hl : Odd l)
    (hll : Nat.ModEq (2 ^ a) (l * l) 1) (hnot : ¬ 2 ^ a ∣ l + 1) :
    (3 ≤ a ∧ ∃ k, l = 4 * k + 1) ∨ ∃ m, l + 1 = 2 ^ (a - 1) * (2 * m + 1) := by
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨r, rfl⟩ := hl
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · by_cases ha3 : 3 ≤ a
    · exact Or.inl ⟨ha3, k, by ring⟩
    · obtain rfl : a = 2 := by omega
      exact Or.inr ⟨k, by ring⟩
  · refine Or.inr ?_
    have h1 : 2 ^ a ∣ 2 * ((2 * k + 1) * (2 * (2 * k + 1) + 1 + 1)) := by
      have e : (2 * (2 * k + 1) + 1) * (2 * (2 * k + 1) + 1) - 1 =
          2 * ((2 * k + 1) * (2 * (2 * k + 1) + 1 + 1)) := Nat.sub_eq_of_eq_add (by ring)
      have := (Nat.modEq_iff_dvd' (by nlinarith)).1 hll.symm
      rwa [e] at this
    rw [h2a] at h1
    have h3 : 2 ^ (a - 1) ∣ 2 * (2 * k + 1) + 1 + 1 :=
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (odd_two_mul_add_one k))).dvd_of_dvd_mul_left
        (Nat.dvd_of_mul_dvd_mul_left two_pos h1)
    obtain ⟨m, hm⟩ := h3
    rcases Nat.even_or_odd m with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · exact absurd ⟨m', by rw [hm, h2a]; ring⟩ hnot
    · exact ⟨m', hm⟩

namespace QData

theorem group_le_centralizer_of_eq_pow (h : QData P S s x a) {t : G} (ht : t = s ^ 2 ^ (a - 1)) :
    QData.group P S x ≤ centralizer ({t} : Set G) := by
  obtain ⟨l, hl, hlodd, -⟩ := h.exists_lambda
  have htS : t ∈ S := by rw [ht, h.S_eq]; exact pow_mem (mem_zpowers s) _
  have htt : t * t = 1 := by
    rw [ht, ← pow_add, ← orderOf_dvd_iff_pow_eq_one, h.orderOf_s, ← two_mul, ← pow_succ']
    exact Nat.pow_dvd_pow 2 (by have := h.two_le; omega)
  have hxt : x * t * x⁻¹ = t := by
    obtain ⟨k, rfl⟩ := hlodd
    rw [ht, ← conj_pow, hl, ← pow_mul, mul_comm, pow_mul, ← ht, pow_succ, pow_mul, pow_two, htt,
      one_pow, one_mul]
  refine sup_le (sup_le (fun p hp => ?_) ?_) ?_
  · exact mem_centralizer_singleton_iff.2 (h.P_comm_S p hp t htS)
  · rw [h.S_eq, zpowers_le, mem_centralizer_singleton_iff, ht]
    exact (Commute.self_pow s _).eq
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hxt]

theorem group_le_centralizer_of_fixed (h : QData P S s x a) {z : G} (hz : z ∈ P)
    (hxz : x * z * x⁻¹ = z) : QData.group P S x ≤ centralizer ({z} : Set G) := by
  refine sup_le (sup_le (fun p hp => ?_) ?_) ?_
  · exact mem_centralizer_singleton_iff.2 (h.P_comm p hp z hz)
  · rw [h.S_eq, zpowers_le, mem_centralizer_singleton_iff]
    exact (h.P_comm_s z hz).symm
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [hxz]

end QData

theorem QData.fusion_values (h : QData P S s x a) (hnot : ¬ x * s * x⁻¹ = s⁻¹) {t : G}
    (ht : t = s ^ 2 ^ (a - 1))
    (hiso : ∀ g : G, g⁻¹ * t * g ∈ QData.group P S x →
      (∀ q ∈ QData.group P S x, q * (g⁻¹ * t * g) = (g⁻¹ * t * g) * q) → g⁻¹ * t * g = t)
    (φ : centralizer ({t} : Set G) →* Multiplicative (ZMod 2))
    (hφP : ∀ y : centralizer ({t} : Set G), (y : G) ∈ P → φ y = 1)
    (hφx : ∀ y : centralizer ({t} : Set G), (y : G) = x → φ y = 1)
    (hφs : ∀ y : centralizer ({t} : Set G), (y : G) = s → φ y = Multiplicative.ofAdd 1)
    (g : G) (b : ℕ) (hb : b ≤ a) (hy : g * s ^ 2 ^ b * g⁻¹ ∈ QData.group P S x)
    (hyH : g * s ^ 2 ^ b * g⁻¹ ∈ centralizer ({t} : Set G)) :
    φ ⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ = if b = 0 then Multiplicative.ofAdd 1 else 1 := by
  have ha := h.two_le
  obtain ⟨l, hl, hlodd, hll⟩ := h.exists_lambda
  have hs_pow : ∀ n : ℕ, s ^ n = 1 ↔ 2 ^ a ∣ n := fun n => by
    rw [← h.orderOf_s, orderOf_dvd_iff_pow_eq_one]
  have hsS : ∀ n : ℕ, s ^ n ∈ S := fun n => by
    rw [h.S_eq]; exact pow_mem (mem_zpowers s) n
  have hQC := h.group_le_centralizer_of_eq_pow ht
  have htS : t ∈ S := ht ▸ hsS _
  have ht1 : t ≠ 1 := by
    rw [ht, Ne, hs_pow, Nat.pow_dvd_pow_iff_le_right (by norm_num)]; omega
  have htt : t * t = 1 := by
    rw [ht, ← pow_add, hs_pow, ← two_mul, ← pow_succ']
    exact Nat.pow_dvd_pow 2 (by omega)
  have ht_even : ∀ n : ℕ, Even n → t ^ n = 1 := by
    rintro n ⟨k, rfl⟩
    rw [← two_mul, pow_mul, pow_two, htt, one_pow]
  have ht_odd : ∀ n : ℕ, Odd n → t ^ n = t := by
    rintro n ⟨k, rfl⟩
    rw [pow_succ, pow_mul, pow_two, htt, one_pow, one_mul]
  have hPC : ∀ p ∈ P, p ∈ centralizer ({t} : Set G) := fun p hp =>
    hQC (mem_sup_left (mem_sup_left hp))
  have hsC : s ∈ centralizer ({t} : Set G) :=
    hQC (mem_sup_left (mem_sup_right (by rw [h.S_eq]; exact mem_zpowers s)))
  have hxC : x ∈ centralizer ({t} : Set G) := hQC (mem_sup_right (mem_zpowers x))
  obtain ⟨p, hp, j, e, he, hyq⟩ := (h.mem_group_iff _).1 hy
  have hφy : φ ⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ = Multiplicative.ofAdd (j : ZMod 2) := by
    have : (⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ : centralizer ({t} : Set G)) =
        ⟨p, hPC p hp⟩ * ⟨s, hsC⟩ ^ j * ⟨x, hxC⟩ ^ e := Subtype.ext (hyq.trans (by simp))
    rw [this, map_mul, map_mul, map_pow, map_pow, hφP ⟨p, hPC p hp⟩ hp, hφs ⟨s, hsC⟩ rfl,
      hφx ⟨x, hxC⟩ rfl, one_pow, one_mul, mul_one, ← ofAdd_nsmul, nsmul_one]
  have hyy : (g * s ^ 2 ^ b * g⁻¹) * (g * s ^ 2 ^ b * g⁻¹) = g * s ^ 2 ^ (b + 1) * g⁻¹ := by
    rw [← pow_two, conj_pow, ← pow_mul, ← pow_succ]
  have hpwy : (g * s ^ 2 ^ b * g⁻¹) ^ 2 ^ (a - 1) = g * s ^ (2 ^ b * 2 ^ (a - 1)) * g⁻¹ := by
    rw [conj_pow, ← pow_mul]
  have h21 : 2 ^ (a - 1) = 2 * 2 ^ (a - 2) := by rw [← pow_succ']; congr 1; omega
  have hpar : ∀ N : ℕ, (g * s ^ 2 ^ b * g⁻¹) ^ 2 ^ (a - 1) = t ^ N → (Even N ↔ Even j) →
      φ ⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ = if b = 0 then Multiplicative.ofAdd 1 else 1 := by
    intro N hN hNj
    rw [hφy]
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have hN1 : t ^ N ≠ 1 := by
        rw [← hN, hpwy, pow_zero, one_mul, ← ht]
        intro h'
        apply ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group
      have hNodd : ¬ Even N := fun hNe => hN1 (ht_even N hNe)
      have hj : Odd j := Nat.not_even_iff_odd.1 fun hje => hNodd (hNj.2 hje)
      rw [ite_eq_left rfl, ZMod.natCast_eq_one_iff_odd.2 hj]
    · have hs1 : s ^ (2 ^ b * 2 ^ (a - 1)) = 1 :=
        (hs_pow _).2 (by rw [← pow_add]; exact Nat.pow_dvd_pow 2 (by omega))
      have hN1 : t ^ N = 1 := by rw [← hN, hpwy, hs1, mul_one, mul_inv_cancel]
      have hNe : Even N := by
        by_contra hne
        exact ht1 ((ht_odd N (Nat.not_even_iff_odd.1 hne)).symm.trans hN1)
      rw [ite_eq_right (by omega), ZMod.natCast_eq_zero_iff_even.2 (hNj.1 hNe), ofAdd_zero]
  have hK : ∀ z : G, (∀ q ∈ QData.group P S x, q * z = z * q) → z ≠ 1 → z * z = 1 →
      (g * s ^ 2 ^ b * g⁻¹) * (g * s ^ 2 ^ b * g⁻¹) = z →
      φ ⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ = if b = 0 then Multiplicative.ofAdd 1 else 1 := by
    intro z hzc hz1 hzz hyz
    have hzQ : z ∈ QData.group P S x := by rw [← hyz]; exact mul_mem hy hy
    have hw : s ^ 2 ^ (b + 1) = g⁻¹ * z * g := by rw [← hyz, hyy]; group
    have hw1 : ¬ a ≤ b + 1 := by
      rw [← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), ← hs_pow, hw]
      intro h'
      apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    have hw2 : a ≤ b + 2 := by
      rw [← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), ← hs_pow,
        show 2 ^ (b + 2) = 2 ^ (b + 1) * 2 by ring, pow_mul, hw, pow_two]
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hzz]; group
    have hzt : z = g * t * g⁻¹ := by
      rw [ht, show a - 1 = b + 1 by omega, hw]; group
    have hgt : g * t * g⁻¹ = t := by
      have := hiso g⁻¹ (by rw [inv_inv, ← hzt]; exact hzQ) (by rw [inv_inv, ← hzt]; exact hzc)
      rwa [inv_inv] at this
    have hgC : g ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [hgt]
    have : (⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ : centralizer ({t} : Set G)) =
        ⟨g, hgC⟩ * ⟨s, hsC⟩ ^ 2 ^ b * (⟨g, hgC⟩)⁻¹ := Subtype.ext (by simp)
    have hconj : φ ⟨g * s ^ 2 ^ b * g⁻¹, hyH⟩ = Multiplicative.ofAdd 1 ^ 2 ^ b := by
      rw [this, map_mul, map_mul, map_inv, map_pow, hφs ⟨s, hsC⟩ rfl]
      exact mul_inv_cancel_comm _ _
    rw [hconj, ← ofAdd_nsmul, nsmul_one]
    split_ifs with hb0
    · simp [hb0]
    · rw [ZMod.natCast_eq_zero_iff_even.2 (Nat.even_pow.2 ⟨even_two, hb0⟩), ofAdd_zero]
  have hcases := odd_mul_self_modEq_one_cases ha hlodd hll fun hd => hnot (by
    rw [hl]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hs_pow]; exact hd))
  obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
  ·
    refine hpar j ?_ Iff.rfl
    rw [hyq, pow_zero, mul_one, h21, pow_mul, pow_two, h.sq_PS hp, ← pow_mul, ht, ← pow_mul, h21]
    congr 1
    ring
  ·
    obtain ⟨c, hc⟩ : ∃ c, c = p * (x * p * x⁻¹) := ⟨_, rfl⟩
    have hcP : c ∈ P := hc ▸ mul_mem hp (h.x_normalizes_P p hp)
    have hyq2 : (g * s ^ 2 ^ b * g⁻¹) * (g * s ^ 2 ^ b * g⁻¹) = c * s ^ (j + l * j) := by
      rw [hyq, pow_one, h.sq_outer hl hp, hc]
    rcases hcases with ⟨ha3, k, hk⟩ | ⟨m, hm⟩
    ·
      refine hpar (j * (2 * k + 1)) ?_ ?_
      · obtain ⟨n, hn⟩ : 2 ∣ 2 ^ (a - 2) := dvd_pow_self 2 (by omega)
        have hcs : Commute c (s ^ (j + l * j)) := h.P_comm_S c hcP _ (hsS _)
        rw [h21, pow_mul, pow_two, hyq2, hcs.mul_pow, hn, pow_mul c, pow_two, h.P_mul_self c hcP,
          one_pow, one_mul, ← pow_mul, ht, ← pow_mul, h21, hn, hk]
        congr 1
        ring
      · rw [Nat.even_mul]
        exact or_iff_left (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k))
    ·
      have hsN : s ^ (j + l * j) = t ^ (j * (2 * m + 1)) := by
        rw [ht, ← pow_mul]
        congr 1
        calc j + l * j = j * (l + 1) := by ring
          _ = _ := by rw [hm]; ring
      rw [hsN] at hyq2
      by_cases hz : c * t ^ (j * (2 * m + 1)) = 1
      ·
        have hc1 : c = 1 := by
          have : c ∈ P ⊓ S := mem_inf.2 ⟨hcP, by
            rw [eq_inv_of_mul_eq_one_left hz]; exact inv_mem (pow_mem htS _)⟩
          rwa [h.P_inf_S, mem_bot] at this
        rw [hc1, one_mul] at hz
        have hj : Even j := by
          by_contra hne
          exact ht1 ((ht_odd _ ((Nat.not_even_iff_odd.1 hne).mul
            (odd_two_mul_add_one m))).symm.trans hz)
        rw [hc1, one_mul, hz, hyy] at hyq2
        have hb1 : a ≤ b + 1 := by
          rw [← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), ← hs_pow]
          calc s ^ 2 ^ (b + 1) = g⁻¹ * (g * s ^ 2 ^ (b + 1) * g⁻¹) * g := by group
            _ = 1 := by rw [hyq2]; group
        rw [hφy, ZMod.natCast_eq_zero_iff_even.2 hj, ofAdd_zero, ite_eq_right (by omega)]
      ·
        have hxc : x * c * x⁻¹ = c := by
          obtain ⟨v, p₀, hvP, -, hv1, -, -, hvx, -, -⟩ := h.exists_v
          rcases h.comm_factor_cases hvP hv1 hvx hp with h1 | h1
          · rw [hc, h1]; group
          · rw [hc, h1, hvx]
        have hcC := h.group_le_centralizer_of_fixed hcP hxc
        have hct : Commute c (t ^ (j * (2 * m + 1))) := h.P_comm_S c hcP _ (pow_mem htS _)
        refine hK _ (fun q hq => ?_) hz ?_ hyq2
        · have hqc : Commute q c := mem_centralizer_singleton_iff.1 (hcC hq)
          have hqt : Commute q t := mem_centralizer_singleton_iff.1 (hQC hq)
          exact (hqc.mul_right (hqt.pow_right _)).eq
        · rw [← pow_two, hct.mul_pow, pow_two c, h.P_mul_self c hcP, one_mul, ← pow_mul,
            ht_even _ (even_two.mul_left _)]

end CFSG.OddStandard
