module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped Pointwise

theorem conj_of_inv_odd {G : Type*} [Group G] (j t : G) (hj : j * j = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (t * j))) :
    ∃ k : ℕ, (t * j) ^ k * j * ((t * j) ^ k)⁻¹ = t := by
  set q := t * j with hq
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hjq : j * q * j⁻¹ = q⁻¹ := by
    rw [hq, mul_inv_rev, htinv, hjinv]
    calc j * (t * j) * j = j * t * (j * j) := by group
      _ = j * t := by rw [hj, mul_one]
  obtain ⟨n, hn⟩ := hodd
  refine ⟨n + 1, ?_⟩
  have h1 : j * q ^ (n + 1) * j⁻¹ = (q⁻¹) ^ (n + 1) := by rw [← conj_pow, hjq]
  have h2 : q ^ (n + 1) * q ^ (n + 1) = q := by
    rw [← pow_add, show n + 1 + (n + 1) = (2 * n + 1) + 1 by ring, pow_succ,
      ← hn, pow_orderOf_eq_one, one_mul]
  calc q ^ (n + 1) * j * (q ^ (n + 1))⁻¹
      = q ^ (n + 1) * (j * q ^ (n + 1) * j⁻¹)⁻¹ * j := by group
    _ = q ^ (n + 1) * ((q⁻¹) ^ (n + 1))⁻¹ * j := by rw [h1]
    _ = q ^ (n + 1) * q ^ (n + 1) * j := by rw [inv_pow, inv_inv]
    _ = t := by rw [h2, hq, mul_assoc, hj, mul_one]

theorem exists_fixed_lift {G : Type*} [Group G] (t q z : G) (hz : orderOf z = 11)
    (ht : t * t = 1) (e k : ℤ) (hte : t * z * t⁻¹ = z ^ e)
    (htk : t * q * t⁻¹ = q * z ^ k) :
    ∃ c : ℤ, t * (q * z ^ c) * t⁻¹ = q * z ^ c := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : ∀ c : ℤ, t * z ^ c * t⁻¹ = z ^ (e * c) := by
    intro c
    rw [← conj_zpow, hte, ← zpow_mul]
  have hq' : ∀ c : ℤ, t * (q * z ^ c) * t⁻¹ = q * z ^ (k + e * c) := by
    intro c
    have : t * (q * z ^ c) * t⁻¹ = (t * q * t⁻¹) * (t * z ^ c * t⁻¹) := by group
    rw [this, htk, hconj, mul_assoc, ← zpow_add]
  have hze : t * (z ^ e) * t⁻¹ = z := by
    have : z ^ e = t * z * t⁻¹ := hte.symm
    rw [this, htinv]
    calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
      _ = z := by rw [ht]; group
  have hee : z ^ (e * e) = z ^ (1 : ℤ) := by rw [zpow_one]; exact (hconj e).symm.trans hze
  have hzorder : ∀ a b : ℤ, z ^ a = z ^ b ↔ ((a : ZMod 11) = b) := by
    intro a b
    rw [zpow_eq_zpow_iff_modEq, hz, ZMod.intCast_eq_intCast_iff]
  have hee' : (e : ZMod 11) * e = 1 := by
    have := (hzorder _ _).1 hee
    simpa using this
  have hk0 : t * (t * q * t⁻¹) * t⁻¹ = q := by
    rw [htinv]
    calc t * (t * q * t) * t = (t * t) * q * (t * t) := by group
      _ = q := by rw [ht]; group
  have hk' : (k : ZMod 11) * (1 + e) = 0 := by
    have h1 := hk0
    rw [htk, hq' k] at h1
    have h2 : z ^ (k + e * k) = z ^ (0 : ℤ) := by
      rw [zpow_zero]
      exact mul_left_cancel (h1.trans (mul_one q).symm)
    have := (hzorder _ _).1 h2
    push_cast at this
    linear_combination this
  have hdec : ∀ x : ZMod 11, x * x = 1 → x = 1 ∨ x = -1 := by decide
  have hdec2 : ∀ x y : ZMod 11, x = 1 → y * (1 + x) = 0 → y = 0 := by decide
  have hdec3 : ∀ y : ZMod 11, y + (-1) * (6 * y) = 6 * y := by decide
  rcases hdec _ hee' with h | h
  · refine ⟨0, ?_⟩
    rw [hq' 0]
    congr 1
    rw [hzorder]
    have hk := hdec2 _ _ h hk'
    simp [hk]
  · refine ⟨6 * k, ?_⟩
    rw [hq' (6 * k)]
    congr 1
    rw [hzorder]
    push_cast
    rw [h]
    exact hdec3 _

theorem isConj_of_card_two_mul_odd {C : Type*} [Group C] [Finite C] (m : ℕ) (hm : Odd m)
    (hC : Nat.card C = 2 * m) {a b : C} (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1)
    (hb1 : b ≠ 1) : IsConj a b := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization 2 = 1 := by
    have h1 : 2 ∣ Nat.card C := ⟨m, hC⟩
    have h3 : ¬ 2 ^ 2 ∣ Nat.card C := by
      intro h
      rw [hC] at h
      obtain ⟨r, hr⟩ := hm
      omega
    have a' := (Nat.Prime.pow_dvd_iff_le_factorization h2.out hCne).mp (show 2 ^ 1 ∣ Nat.card C by simpa using h1)
    have b' : ¬ 2 ≤ (Nat.card C).factorization 2 := fun h =>
      h3 ((Nat.Prime.pow_dvd_iff_le_factorization h2.out hCne).mpr h)
    omega
  have hord : ∀ x : C, x * x = 1 → x ≠ 1 → Nat.card (zpowers x) = 2 := by
    intro x hx hx1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  let Pa : Sylow 2 C := Sylow.ofCard (zpowers a) (by rw [hord a ha ha1, hfac]; norm_num)
  let Pb : Sylow 2 C := Sylow.ofCard (zpowers b) (by rw [hord b hb hb1, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Pa Pb
  have hbP : b ∈ (Pb : Subgroup C) := Subgroup.mem_zpowers b
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbP
  have hbP' : g⁻¹ * b * g ∈ zpowers a := hbP
  obtain ⟨i, hi⟩ := hbP'
  have hoa : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hai : a ^ i = a ^ (i % 2) := by
    have := zpow_mod_orderOf a i
    rw [hoa] at this
    exact_mod_cast this.symm
  have hlt : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hfinal : g⁻¹ * b * g = a := by
    rcases hlt with h | h
    · exfalso
      apply hb1
      have h1 : g⁻¹ * b * g = 1 := by
        have := hi
        simp only at this
        rw [← this, hai, h, zpow_zero]
      have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      rw [this, h1]; group
    · have := hi
      simp only at this
      rw [← this, hai, h, zpow_one]
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  rw [← hfinal]
  group

theorem exists_conj_in_centralizer {G : Type*} [Group G] [Finite G] (u a b : G) (m : ℕ)
    (hm : Odd m) (hC : Nat.card (centralizer ({u} : Set G)) = 2 * m)
    (ha : a * u = u * a) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hb : b * u = u * b) (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    ∃ c : G, c * u = u * c ∧ c * a * c⁻¹ = b := by
  have haC : a ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 ha
  have hbC : b ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hb
  have hconj := isConj_of_card_two_mul_odd (C := centralizer ({u} : Set G)) m hm hC
    (a := ⟨a, haC⟩) (b := ⟨b, hbC⟩) (Subtype.ext ha2) (fun h => ha1 (congrArg Subtype.val h))
    (Subtype.ext hb2) (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  exact ⟨c, (mem_centralizer_singleton_iff.1 c.2), congrArg Subtype.val hc⟩

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
