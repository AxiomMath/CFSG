module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GSThmB

open Subgroup
open scoped commutatorElement

namespace E6

variable {H : Type*} [Group H]

theorem exists_period (Q : Subgroup H) [Finite H] (c : H) :
    ∃ d : ℤ, 0 < d ∧ ∀ j : ℤ, c ^ j ∈ Q ↔ d ∣ j := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ c ^ (n : ℤ) ∈ Q :=
    ⟨orderOf c, orderOf_pos c, by rw [zpow_natCast, pow_orderOf_eq_one]; exact one_mem _⟩
  set n := Nat.find hex with hn
  have hn0 : 0 < n := (Nat.find_spec hex).1
  have hnQ : c ^ (n : ℤ) ∈ Q := (Nat.find_spec hex).2
  refine ⟨n, by exact_mod_cast hn0, fun j => ?_⟩
  have hpow : ∀ s : ℤ, (c ^ (n : ℤ)) ^ s ∈ Q := fun s => zpow_mem hnQ s
  have hsplit : c ^ j = (c ^ (n : ℤ)) ^ (j / n) * c ^ (j % n) := by
    rw [← zpow_mul, ← zpow_add, Int.mul_ediv_add_emod]
  constructor
  · intro hj
    have hr : c ^ (j % n) ∈ Q := by
      have h1 : c ^ (j % n) = ((c ^ (n : ℤ)) ^ (j / n))⁻¹ * c ^ j := by
        rw [hsplit, inv_mul_cancel_left]
      rw [h1]
      exact mul_mem (inv_mem (hpow _)) hj
    have hr0 : 0 ≤ j % n := Int.emod_nonneg _ (by exact_mod_cast hn0.ne')
    have hrn : j % n < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn0)
    by_contra hnd
    have hr1 : j % n ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
    have hpos : 0 < (j % n).toNat := by omega
    have hmin := Nat.find_min' hex (m := (j % n).toNat) ⟨hpos, by
      rw [show (((j % n).toNat : ℕ) : ℤ) = j % n by omega]
      exact hr⟩
    omega
  · rintro ⟨s, rfl⟩
    rw [zpow_mul]
    exact hpow s

theorem inv_mul_mem_of_sq_mem {T Q : Subgroup H} [Finite H]
    (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ c ∈ T, ∀ t ∈ T, ∃ k : ℤ, (c ^ k)⁻¹ * t ∈ Q) {x y : H} (hxT : x ∈ T)
    (hyT : y ∈ T) (hxQ : x ∉ Q) (hyQ : y ∉ Q) (hx2 : x * x ∈ Q) (hy2 : y * y ∈ Q) :
    x⁻¹ * y ∈ Q := by
  obtain ⟨c, hcT, hc⟩ := hcyc
  obtain ⟨d, hd0, hd⟩ := exists_period Q c
  have key : ∀ w ∈ T, w ∉ Q → w * w ∈ Q →
      ∃ m : ℤ, c ^ m * ((c ^ m)⁻¹ * w) = w ∧ (c ^ m)⁻¹ * w ∈ Q ∧ d ∣ 2 * m ∧ ¬ d ∣ m := by
    intro w hwT hwQ hw2
    obtain ⟨m, hm⟩ := hc w hwT
    refine ⟨m, by group, hm, ?_, ?_⟩
    · rw [← hd]
      set q := (c ^ m)⁻¹ * w with hq
      have hw : w = c ^ m * q := by rw [hq]; group
      have hcq : c ^ m * q * (c ^ m)⁻¹ ∈ Q := hQn _ (zpow_mem hcT m) q hm
      have h1 : c ^ (2 * m) = (c ^ m * q * (c ^ m)⁻¹)⁻¹ * (w * w) * q⁻¹ := by
        rw [hw, two_mul, zpow_add]
        group
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hcq) hw2) (inv_mem hm)
    · rw [← hd]
      intro hcm
      apply hwQ
      have : w = c ^ m * ((c ^ m)⁻¹ * w) := by group
      rw [this]
      exact mul_mem hcm hm
  obtain ⟨m, -, hmq, hdm2, hdm⟩ := key x hxT hxQ hx2
  obtain ⟨n, -, hnq, hdn2, hdn⟩ := key y hyT hyQ hy2
  have hdiff : d ∣ n - m := by
    obtain ⟨k, hk⟩ := hdm2
    obtain ⟨l, hl⟩ := hdn2
    have hkodd : Odd k := by
      rcases Int.even_or_odd k with ⟨r, hr⟩ | hk'
      · exfalso
        apply hdm
        refine ⟨r, ?_⟩
        have : 2 * m = 2 * (d * r) := by rw [hk, hr]; ring
        exact mul_left_cancel₀ two_ne_zero this
      · exact hk'
    have hlodd : Odd l := by
      rcases Int.even_or_odd l with ⟨r, hr⟩ | hl'
      · exfalso
        apply hdn
        refine ⟨r, ?_⟩
        have : 2 * n = 2 * (d * r) := by rw [hl, hr]; ring
        exact mul_left_cancel₀ two_ne_zero this
      · exact hl'
    obtain ⟨r, hr⟩ := Odd.sub_odd hlodd hkodd
    refine ⟨r, ?_⟩
    have : 2 * (n - m) = 2 * (d * r) := by
      rw [mul_sub, hk, hl, ← mul_sub, show l - k = r + r by rw [hr]]
      ring
    exact mul_left_cancel₀ two_ne_zero this
  have hcnm : c ^ (n - m) ∈ Q := (hd _).mpr hdiff
  have h1 : x⁻¹ * y = ((c ^ m)⁻¹ * x)⁻¹ * c ^ (n - m) * ((c ^ n)⁻¹ * y) := by
    rw [zpow_sub]
    group
  rw [h1]
  exact mul_mem (mul_mem (inv_mem hmq) hcnm) hnq

theorem le_of_perfect {M N : Subgroup H} (hM : ⁅M, M⁆ = M) (hN : N.Normal)
    (hNcyc : IsCyclic (H ⧸ N)) : M ≤ N := by
  rw [← hM, commutator_le]
  intro g₁ _ g₂ _
  have hcomm : (QuotientGroup.mk' N g₁) * QuotientGroup.mk' N g₂ =
      QuotientGroup.mk' N g₂ * QuotientGroup.mk' N g₁ :=
    (IsCyclic.commGroup (α := H ⧸ N)).mul_comm _ _
  have h1 : QuotientGroup.mk' N ⁅g₁, g₂⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

variable [Finite H]

theorem mem_of_transfer {T Q : Subgroup H} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ c ∈ T, ∀ t ∈ T, ∃ k : ℤ, (c ^ k)⁻¹ * t ∈ Q)
    (hQN : ∀ (N : Subgroup H) [N.Normal], IsCyclic (H ⧸ N) → Q ≤ N) {b : H} (hbT : b ∈ T)
    (hbQ : b ∉ Q) (hbb : b * b = 1) (hconj : ∀ g : H, g⁻¹ * b * g ∉ Q) {t : H} (htT : t ∈ T)
    (htN : ∀ (N : Subgroup H) [N.Normal], IsCyclic (H ⧸ N) → t ∈ N) : t ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2Q : b * b ∈ Q := by rw [hbb]; exact one_mem _
  have htr := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hbT
    hbQ (fun g k _ => by
      rw [pow_mul, sq, hbb, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hg _ => by
      right
      have hg2 : g⁻¹ * b * g * (g⁻¹ * b * g) ∈ Q := by
        rw [show g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g by group, hbb,
          show g⁻¹ * 1 * g = 1 by group]
        exact one_mem _
      exact inv_mul_mem_of_sq_mem hQn hcyc hbT hg hbQ (hconj g) hb2Q hg2)
  obtain ⟨N, hNn, hNcyc, -, hbN⟩ | ⟨g, hg, -⟩ := htr
  · have htN' := htN N hNcyc
    have hQN' := hQN N hNcyc
    by_contra htQ
    obtain ⟨r, hr⟩ := IsPGroup.iff_orderOf.mp hT ⟨t, htT⟩
    have htr : t ^ 2 ^ r = 1 := by
      have := pow_orderOf_eq_one (⟨t, htT⟩ : T)
      rw [hr] at this
      exact congrArg Subtype.val this
    have hex : ∃ j : ℕ, t ^ 2 ^ j ∈ Q := ⟨r, by rw [htr]; exact one_mem _⟩
    classical
    set j := Nat.find hex with hj
    have hj0 : j ≠ 0 := by
      intro h0
      apply htQ
      have := Nat.find_spec hex
      rw [← hj, h0, pow_zero, pow_one] at this
      exact this
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hxQ : t ^ 2 ^ i ∉ Q := Nat.find_min hex (by omega)
    have hx2 : t ^ 2 ^ i * t ^ 2 ^ i ∈ Q := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      have := Nat.find_spec hex
      rwa [← hj, hi] at this
    have h1 := inv_mul_mem_of_sq_mem hQn hcyc (pow_mem htT _) hbT hxQ hbQ hx2 hb2Q
    apply hbN
    have : b = t ^ 2 ^ i * ((t ^ 2 ^ i)⁻¹ * b) := by group
    rw [this]
    exact mul_mem (pow_mem htN' _) (hQN' h1)
  · exact absurd hg (hconj g)

end E6

end CFSG.ComponentClassification.GSThmB
