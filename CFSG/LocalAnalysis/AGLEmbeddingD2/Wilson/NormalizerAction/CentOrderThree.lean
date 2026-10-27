module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.FrattiniSub
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import Mathlib.Data.Int.Star

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

variable {G : Type*} [Group G]

section Setup

variable (Q : Subgroup G) (c z : G)

theorem mem_form_of_normalizes (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1) {x : G}
    (hx : x ∈ Q ⊔ zpowers c) : ∃ k : ℤ, ∃ q ∈ Q, x = c ^ k * q := by
  have hn : c ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcQ h hh, fun hh => ?_⟩
    have h3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    have h2 := hcQ _ (hcQ _ hh)
    have e : c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = h := by
      have e : c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * h * (c * c * c)⁻¹ := by group
      rw [e, h3']; group
    rwa [e] at h2
  have hle : zpowers c ≤ normalizer (Q : Set G) := zpowers_le.2 hn
  have h := coe_mul_of_left_le_normalizer_right (zpowers c) Q hle
  have hx' : x ∈ (↑(zpowers c ⊔ Q) : Set G) := by rw [sup_comm]; exact hx
  rw [h] at hx'
  obtain ⟨a, ha, q, hq, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  exact ⟨k, q, hq, rfl⟩

theorem zpow_conj_mem (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1) (k : ℤ) {q : G}
    (hq : q ∈ Q) : c ^ k * q * (c ^ k)⁻¹ ∈ Q := by
  have hn : c ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcQ h hh, fun hh => ?_⟩
    have h3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    have h2 := hcQ _ (hcQ _ hh)
    have e : c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = h := by
      have e : c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * h * (c * c * c)⁻¹ := by group
      rw [e, h3']; group
    rwa [e] at h2
  exact (mem_normalizer_iff.1 (zpow_mem hn k) q).1 hq

theorem zpow_mem_eq_one (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {n : ℕ} (hn : Nat.Coprime 3 n)
    (hQ : Nat.card Q = n) {m : ℤ} (h : c ^ m ∈ Q) : c ^ m = 1 := by
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have h1 : zpowers c ⊓ Q = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have a := Subgroup.card_dvd_of_le (inf_le_right : zpowers c ⊓ Q ≤ Q)
    have b := Subgroup.card_dvd_of_le (inf_le_left : zpowers c ⊓ Q ≤ zpowers c)
    rw [hQ] at a
    rw [Nat.card_zpowers, hord] at b
    have : Nat.card ↥(zpowers c ⊓ Q) ∣ Nat.gcd 3 n := Nat.dvd_gcd b a
    rw [hn] at this
    exact Nat.dvd_one.1 this
  have : c ^ m ∈ zpowers c ⊓ Q := ⟨mem_zpowers_iff.2 ⟨m, rfl⟩, h⟩
  rw [h1] at this
  exact mem_bot.1 this

theorem centralizer_K_eq (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1)
    (hz2 : z * z = 1) (hzQ : z ∈ Q) (hzc : Commute z c)
    (hCQ : ∀ q ∈ Q, q * c = c * q → q ∈ zpowers z) :
    (Q ⊔ zpowers c) ⊓ centralizer ({c} : Set G) = zpowers (z * c) := by
  have hz0K : z ∈ Q ⊔ zpowers c := (le_sup_left : Q ≤ Q ⊔ zpowers c) hzQ
  have hcK : c ∈ Q ⊔ zpowers c := (le_sup_right : zpowers c ≤ Q ⊔ zpowers c) (mem_zpowers c)
  apply le_antisymm
  · rintro x ⟨hxK, hxc⟩
    obtain ⟨k, q, hq, rfl⟩ := mem_form_of_normalizes Q c hcQ hc3 hxK
    have hqc : q * c = c * q := by
      have h1 : c ^ k * q * c = c * (c ^ k * q) := mem_centralizer_singleton_iff.1 hxc
      have h2 : c ^ k * (c * q) = c ^ k * (q * c) := by
        calc c ^ k * (c * q) = c * (c ^ k * q) := by
              rw [← mul_assoc, ← mul_assoc, (Commute.self_zpow c k).symm.eq]
          _ = c ^ k * q * c := h1.symm
          _ = c ^ k * (q * c) := by rw [mul_assoc]
      exact (mul_left_cancel h2).symm
    obtain ⟨e, he⟩ := mem_zpowers_iff.1 (hCQ q hq hqc)
    refine mem_zpowers_iff.2 ⟨4 * k + 3 * e, ?_⟩
    have e1 : z ^ (4 * k + 3 * e) = z ^ e := by
      have hz : z ^ 2 = 1 := by rw [pow_two]; exact hz2
      have : 4 * k + 3 * e = 2 * (2 * k + e) + e := by ring
      rw [this, zpow_add, zpow_mul]
      simp [hz]
    have e2 : c ^ (4 * k + 3 * e) = c ^ k := by
      have : 4 * k + 3 * e = 3 * (k + e) + k := by ring
      rw [this, zpow_add, zpow_mul]
      simp [hc3]
    calc (z * c) ^ (4 * k + 3 * e) = z ^ (4 * k + 3 * e) * c ^ (4 * k + 3 * e) :=
          hzc.mul_zpow _
      _ = z ^ e * c ^ k := by rw [e1, e2]
      _ = c ^ k * z ^ e := (hzc.zpow_zpow e k).eq
      _ = c ^ k * q := by rw [he]
  · rw [zpowers_le]
    refine ⟨mul_mem hz0K hcK, ?_⟩
    have h : z * c * c = c * (z * c) := by
      calc z * c * c = c * z * c := by rw [← hzc.eq]
        _ = c * (z * c) := mul_assoc _ _ _
    exact mem_centralizer_singleton_iff.2 h

theorem card_centralizer_K (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzQ : z ∈ Q) (hzc : Commute z c)
    (hCQ : ∀ q ∈ Q, q * c = c * q → q ∈ zpowers z) :
    Nat.card ↥((Q ⊔ zpowers c) ⊓ centralizer ({c} : Set G)) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  rw [centralizer_K_eq Q c z hcQ hc3 hz2 hzQ hzc hCQ, Nat.card_zpowers,
    hzc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hz, hc]; norm_num), hz, hc]

theorem K_normalizer_centralizes (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {n : ℕ} (hn : Nat.Coprime 3 n) (hQ : Nat.card Q = n) {x : G} (hxK : x ∈ Q ⊔ zpowers c)
    (hxN : x ∈ normalizer ((zpowers c : Subgroup G) : Set G)) : x * c = c * x := by
  obtain ⟨k, q, hq, rfl⟩ := mem_form_of_normalizes Q c hcQ hc3 hxK
  have h1 : c ^ k * q * c * (c ^ k * q)⁻¹ ∈ zpowers c :=
    (mem_normalizer_iff.1 hxN c).1 (mem_zpowers c)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
  have hd : q * c * q⁻¹ * c⁻¹ ∈ Q := by
    have := Q.mul_mem hq (hcQ q⁻¹ (Q.inv_mem hq))
    have e : q * (c * q⁻¹ * c⁻¹) = q * c * q⁻¹ * c⁻¹ := by group
    rwa [e] at this
  have hd' := zpow_conj_mem Q c hcQ hc3 k hd
  have hc : Commute (c ^ k) c := (Commute.self_zpow c k).symm
  have e2 : c ^ k * q * c * (c ^ k * q)⁻¹ =
      (c ^ k * (q * c * q⁻¹ * c⁻¹) * (c ^ k)⁻¹) * c := by
    have : c ^ k * (q * c * q⁻¹ * c⁻¹) * (c ^ k)⁻¹ * c =
        c ^ k * (q * c * q⁻¹) * (c⁻¹ * (c ^ k)⁻¹ * c) := by group
    rw [this]
    have h3 : c⁻¹ * (c ^ k)⁻¹ * c = (c ^ k)⁻¹ := by
      have : (c ^ k)⁻¹ * c = c * (c ^ k)⁻¹ := (Commute.inv_left hc).eq
      calc c⁻¹ * (c ^ k)⁻¹ * c = c⁻¹ * ((c ^ k)⁻¹ * c) := mul_assoc _ _ _
        _ = c⁻¹ * (c * (c ^ k)⁻¹) := by rw [this]
        _ = (c ^ k)⁻¹ := by group
    rw [h3]; group
  have hm : c ^ (j - 1) ∈ Q := by
    have e3 : c ^ (j - 1) = c ^ k * (q * c * q⁻¹ * c⁻¹) * (c ^ k)⁻¹ := by
      rw [zpow_sub_one, hj, e2]; group
    rw [e3]; exact hd'
  have h1' := zpow_mem_eq_one Q c hc3 hc1 hn hQ hm
  have hjc : c ^ j = c := by
    rw [zpow_sub_one] at h1'
    exact mul_inv_eq_one.1 h1'
  rw [hjc] at hj
  calc c ^ k * q * c = (c ^ k * q * c * (c ^ k * q)⁻¹) * (c ^ k * q) := by group
    _ = c * (c ^ k * q) := by rw [← hj]

theorem K_inf_normalizer (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {n : ℕ} (hn : Nat.Coprime 3 n) (hQ : Nat.card Q = n) :
    (Q ⊔ zpowers c) ⊓ normalizer ((zpowers c : Subgroup G) : Set G) =
      (Q ⊔ zpowers c) ⊓ centralizer ({c} : Set G) := by
  ext x
  constructor
  · rintro ⟨hK, hN⟩
    exact ⟨hK, mem_centralizer_singleton_iff.2
      (K_normalizer_centralizes Q c hcQ hc3 hc1 hn hQ hK hN)⟩
  · rintro ⟨hK, hC⟩
    refine ⟨hK, ?_⟩
    have hc : x * c = c * x := mem_centralizer_singleton_iff.1 hC
    have hconj : x * c * x⁻¹ = c := by rw [hc]; group
    have hconj' : x⁻¹ * c * x = c := by
      calc x⁻¹ * c * x = x⁻¹ * (x * c * x⁻¹) * x := by rw [hconj]
        _ = c := by group
    refine mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by rw [← conj_zpow, hconj]⟩
    · rintro ⟨m, hm⟩
      have hm' : c ^ m = x * h * x⁻¹ := hm
      have e : x⁻¹ * c ^ m * x = c ^ m := by
        have := conj_zpow (a := x⁻¹) (b := c) (i := m)
        simp only [inv_inv] at this
        rw [← this, hconj']
      refine ⟨m, ?_⟩
      show c ^ m = h
      calc c ^ m = x⁻¹ * c ^ m * x := e.symm
        _ = x⁻¹ * (x * h * x⁻¹) * x := by rw [hm']
        _ = h := by group

theorem centralizer_le_normalizer_zpowers {x : G} (hC : x ∈ centralizer ({c} : Set G)) :
    x ∈ normalizer ((zpowers c : Subgroup G) : Set G) := by
  have hc : x * c = c * x := mem_centralizer_singleton_iff.1 hC
  have hconj : x * c * x⁻¹ = c := by rw [hc]; group
  have hconj' : x⁻¹ * c * x = c := by
    calc x⁻¹ * c * x = x⁻¹ * (x * c * x⁻¹) * x := by rw [hconj]
      _ = c := by group
  refine mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [← conj_zpow, hconj]⟩
  · rintro ⟨m, hm⟩
    have hm' : c ^ m = x * h * x⁻¹ := hm
    have e : x⁻¹ * c ^ m * x = c ^ m := by
      have := conj_zpow (a := x⁻¹) (b := c) (i := m)
      simp only [inv_inv] at this
      rw [← this, hconj']
    refine ⟨m, ?_⟩
    show c ^ m = h
    calc c ^ m = x⁻¹ * c ^ m * x := e.symm
      _ = x⁻¹ * (x * h * x⁻¹) * x := by rw [hm']
      _ = h := by group

theorem zpow_cases (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {j : ℤ} (hj : c ^ j ≠ 1) :
    c ^ j = c ∨ c ^ j = c⁻¹ := by
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have h := zpow_mod_orderOf c j
  rw [hord] at h
  have : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases this with h0 | h1 | h2
  · exfalso; apply hj; rw [← h]; simp [show ((3 : ℕ) : ℤ) = 3 from rfl, h0]
  · left; rw [← h]; simp [show ((3 : ℕ) : ℤ) = 3 from rfl, h1]
  · right
    rw [← h]
    simp only [Nat.cast_ofNat, h2]
    have : c ^ (2 : ℤ) = c ^ 2 := zpow_ofNat c 2
    rw [this]
    have : c * c * c = 1 := by simpa [pow_succ] using hc3
    rw [pow_two]
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using this)

theorem card_normalizer_eq_two_mul (M : Subgroup G) [Finite G] (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {h : G}
    (hhM : h ∈ M) (hinv : h * c * h⁻¹ = c⁻¹) :
    Nat.card ↥(M ⊓ normalizer ((zpowers c : Subgroup G) : Set G)) =
      2 * Nat.card ↥(M ⊓ centralizer ({c} : Set G)) := by
  have hcc : c ≠ c⁻¹ := by
    intro h2
    have : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel c
    have h3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    rw [this, one_mul] at h3'
    exact hc1 h3'
  set N₀ := M ⊓ normalizer ((zpowers c : Subgroup G) : Set G) with hN₀
  set C₀ := M ⊓ centralizer ({c} : Set G) with hC₀
  have hCN : C₀ ≤ N₀ := fun x hx => ⟨hx.1, centralizer_le_normalizer_zpowers c hx.2⟩
  have hhc : h * c = c⁻¹ * h := by
    calc h * c = (h * c * h⁻¹) * h := by group
      _ = c⁻¹ * h := by rw [hinv]
  have hh' : h⁻¹ * c * h = c⁻¹ := by
    have e : h⁻¹ * c⁻¹ * h = c := by
      calc h⁻¹ * c⁻¹ * h = h⁻¹ * (h * c * h⁻¹) * h := by rw [hinv]
        _ = c := by group
    calc h⁻¹ * c * h = (h⁻¹ * c⁻¹ * h)⁻¹ := by group
      _ = c⁻¹ := by rw [e]
  have hidx : C₀.relIndex N₀ = 2 := by
    rw [relIndex, index_eq_two_iff]
    have hhN : h ∈ N₀ := by
      refine ⟨hhM, mem_normalizer_iff.2 fun y => ⟨?_, ?_⟩⟩
      · rintro ⟨m, rfl⟩
        refine ⟨-m, ?_⟩
        show c ^ (-m) = h * c ^ m * h⁻¹
        rw [← conj_zpow, hinv, inv_zpow']
      · rintro ⟨m, hm⟩
        refine ⟨-m, ?_⟩
        have hm' : c ^ m = h * y * h⁻¹ := hm
        show c ^ (-m) = y
        have e := conj_zpow (a := h⁻¹) (b := c) (i := m)
        rw [inv_inv, hh'] at e
        calc c ^ (-m) = (c⁻¹) ^ m := (inv_zpow' c m).symm
          _ = h⁻¹ * c ^ m * h := e
          _ = y := by rw [hm']; group
    refine ⟨⟨h, hhN⟩, fun b => ?_⟩
    rw [xor_iff_iff_not]
    have hbN := b.2
    set bb : G := (b : G) with hbb
    have hbc : bb * c * bb⁻¹ ∈ zpowers c :=
      (mem_normalizer_iff.1 hbN.2 c).1 (mem_zpowers c)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hbc
    have hne : c ^ j ≠ 1 := by
      intro h1
      rw [hj] at h1
      apply hc1
      calc c = bb⁻¹ * (bb * c * bb⁻¹) * bb := by group
        _ = 1 := by rw [h1]; group
    have hmemC : ∀ y : N₀, y ∈ C₀.subgroupOf N₀ ↔ (y : G) * c = c * (y : G) := by
      intro y
      rw [mem_subgroupOf]
      exact ⟨fun hy => mem_centralizer_singleton_iff.1 hy.2,
        fun hy => ⟨y.2.1, mem_centralizer_singleton_iff.2 hy⟩⟩
    rw [hmemC, hmemC]
    show (bb * h) * c = c * (bb * h) ↔ ¬ (bb * c = c * bb)
    rcases zpow_cases c hc3 hc1 hne with hcj | hcj
    ·
      have hbcb : bb * c * bb⁻¹ = c := by rw [← hj]; exact hcj
      have hb1 : bb * c = c * bb := by
        calc bb * c = (bb * c * bb⁻¹) * bb := by group
          _ = c * bb := by rw [hbcb]
      have hb1i : bb * c⁻¹ = c⁻¹ * bb := by
        calc bb * c⁻¹ = (bb * c * bb⁻¹)⁻¹ * bb := by group
          _ = c⁻¹ * bb := by rw [hbcb]
      have hb2 : ¬ ((bb * h) * c = c * (bb * h)) := by
        intro h2
        have e : bb * h * c = c⁻¹ * (bb * h) := by
          calc bb * h * c = bb * (h * c) := mul_assoc _ _ _
            _ = bb * (c⁻¹ * h) := by rw [hhc]
            _ = (bb * c⁻¹) * h := (mul_assoc _ _ _).symm
            _ = (c⁻¹ * bb) * h := by rw [hb1i]
            _ = c⁻¹ * (bb * h) := mul_assoc _ _ _
        rw [e] at h2
        exact hcc (mul_right_cancel h2).symm
      exact ⟨fun h2 => absurd h2 hb2, fun h2 => absurd hb1 h2⟩
    ·
      have hbcb : bb * c * bb⁻¹ = c⁻¹ := by rw [← hj]; exact hcj
      have hb1 : bb * c = c⁻¹ * bb := by
        calc bb * c = (bb * c * bb⁻¹) * bb := by group
          _ = c⁻¹ * bb := by rw [hbcb]
      have hb2 : ¬ (bb * c = c * bb) := by
        intro h2
        rw [hb1] at h2
        exact hcc (mul_right_cancel h2).symm
      have hb1' : bb * c⁻¹ = c * bb := by
        calc bb * c⁻¹ = (bb * c * bb⁻¹)⁻¹ * bb := by group
          _ = c * bb := by rw [hbcb, inv_inv]
      have hb3 : (bb * h) * c = c * (bb * h) := by
        calc bb * h * c = bb * (h * c) := mul_assoc _ _ _
          _ = bb * (c⁻¹ * h) := by rw [hhc]
          _ = (bb * c⁻¹) * h := (mul_assoc _ _ _).symm
          _ = (c * bb) * h := by rw [hb1']
          _ = c * (bb * h) := mul_assoc _ _ _
      exact ⟨fun _ => hb2, fun _ => hb3⟩
  have := relIndex_mul_card (H := C₀) (K := N₀)
  rw [inf_of_le_left hCN, hidx] at this
  exact this.symm

theorem card_centralizer_mul_card (M : Subgroup G) [Finite G] (hcQ : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hQcard : Nat.card Q = 2 ^ 13)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzQ : z ∈ Q) (hzc : Commute z c)
    (hCQ : ∀ q ∈ Q, q * c = c * q → q ∈ zpowers z)
    (hKM : Q ⊔ zpowers c ≤ M) (hKn : ((Q ⊔ zpowers c).subgroupOf M).Normal)
    (hKcard : Nat.card ↥(Q ⊔ zpowers c) = 3 * 2 ^ 13) {h : G} (hhM : h ∈ M)
    (hinv : h * c * h⁻¹ = c⁻¹) :
    Nat.card ↥(M ⊓ centralizer ({c} : Set G)) * 2 * (3 * 2 ^ 13) = Nat.card M * 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (2 ^ 13) := by norm_num
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hPcard : Nat.card (zpowers c) =
      3 ^ (Nat.card ↥(Q ⊔ zpowers c)).factorization 3 := by
    rw [Nat.card_zpowers, hord, hKcard,
      show 3 * 2 ^ 13 = 3 ^ 1 * 2 ^ 13 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 1 (by norm_num)]
    norm_num
  have hF := card_inf_normalizer_mul_card (p := 3) M (Q ⊔ zpowers c) (zpowers c) hKM hKn
    le_sup_right hPcard
  rw [K_inf_normalizer Q c hcQ hc3 hc1 hcop hQcard,
    card_centralizer_K Q c z hcQ hc3 hc1 hz2 hz1 hzQ hzc hCQ,
    card_normalizer_eq_two_mul c M hc3 hc1 hhM hinv, hKcard] at hF
  linarith

end Setup

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
