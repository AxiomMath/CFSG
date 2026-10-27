module

public import CFSG.LocalAnalysis.GH72.Sec5Config
import CFSG.RankThree.PartTwo.Sec18.Item188Abs
import CFSG.GroupTheory.OddInversion
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement Pointwise

section FourGroup

variable {G : Type} [Group G]

theorem commutator_ne_self_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}
    (hD : IsPGroup p D) (hD1 : D ≠ ⊥) : ⁅D, D⁆ ≠ D := by
  intro h
  have : Group.IsNilpotent D := hD.isNilpotent
  have : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD1
  refine (IsSolvable.commutator_lt_top_of_nontrivial D).ne ?_
  apply map_injective D.subtype_injective
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, h]

theorem mul_comm_of_conj_eq_of_conj_eq_inv {B D : Subgroup G} (hD : Odd (Nat.card D))
    (hDB : ⁅D, D⁆ ≤ centralizer (B : Set G)) (hDD : ⁅D, ⁅D, D⁆⁆ = ⊥) {t a b : G} (ht : t ∈ B)
    (ha : a ∈ D) (hb : b ∈ D) (hta : t * a * t⁻¹ = a) (htb : t * b * t⁻¹ = b⁻¹) :
    a * b = b * a := by
  have hc : ⁅a, b⁆ ∈ ⁅D, D⁆ := commutator_mem_commutator ha hb
  have htc : t * ⁅a, b⁆ * t⁻¹ = ⁅a, b⁆ := by
    have := mem_centralizer_iff.mp (hDB hc) t ht
    rw [this, mul_inv_cancel_right]
  have hbc : b * ⁅a, b⁆ = ⁅a, b⁆ * b := by
    have h := commutator_mem_commutator hb hc
    rw [hDD, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hconj : t * ⁅a, b⁆ * t⁻¹ = a * b⁻¹ * a⁻¹ * b := by
    rw [commutatorElement_def]
    calc t * (a * b * a⁻¹ * b⁻¹) * t⁻¹ =
        (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by group
      _ = a * b⁻¹ * a⁻¹ * b := by rw [hta, htb, inv_inv]
  have hinv : ⁅a, b⁆⁻¹ = ⁅a, b⁆ := by
    calc ⁅a, b⁆⁻¹ = b * (a * b⁻¹ * a⁻¹ * b) * b⁻¹ := by rw [commutatorElement_def]; group
      _ = b * ⁅a, b⁆ * b⁻¹ := by rw [← hconj, htc]
      _ = ⁅a, b⁆ := by rw [hbc, mul_inv_cancel_right]
  have h1 : ⁅a, b⁆ = 1 :=
    OddInversion.sq_injOn hD (commutator_le_left_of_le_normalizer le_normalizer hc) (one_mem _)
      (by rw [sq, one_pow]; nth_rewrite 1 [← hinv]; exact inv_mul_cancel _)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem fixed_inverted_of_mul_ne {B D : Subgroup G} (hB : IsKleinFour B)
    (hBD : B ≤ normalizer (D : Set G)) {b s d : G} (hb : b ∈ B) (hb1 : b ≠ 1) (hs : s ∈ B)
    (hd : d ∈ D) (hdb : d * b = b * d) (hsd : s * d ≠ d * s) :
    s ∉ zpowers b ∧ ∃ x ∈ D, x ≠ 1 ∧ b * x * b⁻¹ = x ∧
      ∀ s' ∈ B, s' ∉ zpowers b → s' * x * s'⁻¹ = x⁻¹ := by
  have hb2 : orderOf b = 2 := orderOf_eq_two_of_isKleinFour hB hb hb1
  have hsb : s ∉ zpowers b := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers hb2 h with rfl | rfl
    · exact hsd (by group)
    · exact hsd hdb.symm
  have hs1 : s ≠ 1 := fun h => hsb (h ▸ one_mem _)
  have hs2 : orderOf s = 2 := orderOf_eq_two_of_isKleinFour hB hs hs1
  have hx := OddInversion.mul_conj_inv_mem_invertedSet hs2 (hBD hs) hd
  have hbs : b * s = s * b := mul_comm_of_isKleinFour hB hb hs
  have hbd : b * d * b⁻¹ = d := by rw [← hdb, mul_inv_cancel_right]
  have hbx : b * (d * (s * d * s⁻¹)⁻¹) * b⁻¹ = d * (s * d * s⁻¹)⁻¹ := by
    have hbsd : b * (s * d * s⁻¹) * b⁻¹ = s * d * s⁻¹ := by
      calc b * (s * d * s⁻¹) * b⁻¹ = (b * s) * d * (b * s)⁻¹ := by group
        _ = (s * b) * d * (s * b)⁻¹ := by rw [hbs]
        _ = s * (b * d * b⁻¹) * s⁻¹ := by group
        _ = s * d * s⁻¹ := by rw [hbd]
    calc b * (d * (s * d * s⁻¹)⁻¹) * b⁻¹ = (b * d * b⁻¹) * (b * (s * d * s⁻¹) * b⁻¹)⁻¹ := by
          group
      _ = d * (s * d * s⁻¹)⁻¹ := by rw [hbd, hbsd]
  refine ⟨hsb, d * (s * d * s⁻¹)⁻¹, hx.1, fun h => hsd ?_, hbx, fun s' hs' hs'b => ?_⟩
  · have h' : s * d * s⁻¹ = d := (mul_inv_eq_one.mp h).symm
    calc s * d = s * d * s⁻¹ * s := by group
      _ = d * s := by rw [h']
  · rcases eq_or_eq_mul_of_not_mem_zpowers hB hb hb1 hs hsb hs' hs'b with rfl | rfl
    · exact hx.2
    · calc b * s * (d * (s * d * s⁻¹)⁻¹) * (b * s)⁻¹ =
            b * (s * (d * (s * d * s⁻¹)⁻¹) * s⁻¹) * b⁻¹ := by group
        _ = b * (d * (s * d * s⁻¹)⁻¹)⁻¹ * b⁻¹ := by rw [hx.2]
        _ = (b * (d * (s * d * s⁻¹)⁻¹) * b⁻¹)⁻¹ := by group
        _ = (d * (s * d * s⁻¹)⁻¹)⁻¹ := by rw [hbx]

section FourGroupAction

variable [Finite G] {B D : Subgroup G} (hB : IsKleinFour B) (hD : Odd (Nat.card D))
  (hBD : B ≤ normalizer (D : Set G))
include hB hD hBD

theorem exists_fixed_inverted_of_isKleinFour (hDB : ¬ D ≤ centralizer (B : Set G)) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ x ∈ D, x ≠ 1 ∧ b * x * b⁻¹ = x ∧
      ∀ s ∈ B, s ∉ zpowers b → s * x * s⁻¹ = x⁻¹ := by
  by_contra hcon
  apply hDB
  refine le_of_forall_inf_C_le_of_isKleinFour hB hD hBD fun b hb hb1 => ?_
  rintro d ⟨hdD, hdb⟩
  rw [mem_centralizer_iff]
  intro s hs
  by_contra hsd
  obtain ⟨-, hx⟩ := fixed_inverted_of_mul_ne hB hBD hb hb1 hs hdD
    (mem_centralizer_singleton_iff.mp hdb) hsd
  exact hcon ⟨b, hb, hb1, hx⟩

theorem exists_fixed_inverted_of_not_le_C {c : G} (hc : c ∈ B) (hDc : ¬ D ≤ C c) :
    ∃ b ∈ B, b ≠ 1 ∧ c ∉ zpowers b ∧ ∃ x ∈ D, x ≠ 1 ∧ b * x * b⁻¹ = x ∧
      ∀ s ∈ B, s ∉ zpowers b → s * x * s⁻¹ = x⁻¹ := by
  by_contra hcon
  apply hDc
  refine le_of_forall_inf_C_le_of_isKleinFour hB hD hBD fun b hb hb1 => ?_
  rintro d ⟨hdD, hdb⟩
  rw [mem_centralizer_singleton_iff]
  by_contra hdc
  obtain ⟨hcb, hx⟩ := fixed_inverted_of_mul_ne hB hBD hb hb1 hc hdD
    (mem_centralizer_singleton_iff.mp hdb) fun h => hdc h.symm
  exact hcon ⟨b, hb, hb1, hcb, hx⟩

end FourGroupAction

theorem conj_fixed_inverted {B : Subgroup G} {u b x : G} (hu : u ∈ normalizer (B : Set G))
    (hbx : b * x * b⁻¹ = x) (hx : ∀ s ∈ B, s ∉ zpowers b → s * x * s⁻¹ = x⁻¹) :
    (u * b * u⁻¹) * (u * x * u⁻¹) * (u * b * u⁻¹)⁻¹ = u * x * u⁻¹ ∧
      ∀ s ∈ B, s ∉ zpowers (u * b * u⁻¹) → s * (u * x * u⁻¹) * s⁻¹ = (u * x * u⁻¹)⁻¹ := by
  refine ⟨?_, fun s hs hsb => ?_⟩
  · calc (u * b * u⁻¹) * (u * x * u⁻¹) * (u * b * u⁻¹)⁻¹ = u * (b * x * b⁻¹) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hbx]
  · have hs' : u⁻¹ * s * u ∈ B := by
      have := (mem_normalizer_iff.mp (inv_mem hu) s).mp hs
      simpa using this
    have hsb' : u⁻¹ * s * u ∉ zpowers b := by
      intro h
      apply hsb
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
      refine mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [conj_zpow, hn]
      group
    have h := hx _ hs' hsb'
    calc s * (u * x * u⁻¹) * s⁻¹ = u * ((u⁻¹ * s * u) * x * (u⁻¹ * s * u)⁻¹) * u⁻¹ := by group
      _ = (u * x * u⁻¹)⁻¹ := by rw [h]; group

theorem isElemAbelian_zpowers_sup_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z₁ z₂ t : G}
    (h12 : Commute z₁ z₂) (hz₁ : orderOf z₁ = p) (hz₂ : orderOf z₂ = p)
    (ht₁ : t * z₁ * t⁻¹ = z₁) (ht₂ : t * z₂ * t⁻¹ = z₂⁻¹) :
    CFSG.Open.IsElemAbelian p (zpowers z₁ ⊔ zpowers z₂) ∧
      Nat.card (zpowers z₁ ⊔ zpowers z₂ : Subgroup G) = p ^ 2 := by
  have hc : ∀ {a b : G}, Commute a b → zpowers b ≤ centralizer (zpowers a : Set G) := by
    intro a b hab
    rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
    exact (hab.zpow_left n).eq
  have hN12 : zpowers z₂ ≤ normalizer ((zpowers z₁ : Subgroup G) : Set G) :=
    (hc h12).trans (centralizer_le_normalizer _)
  have H12 : zpowers z₁ ⊓ zpowers z₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw1
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hw2
    have h1 : t * z₁ ^ m * t⁻¹ = z₁ ^ m := by rw [← conj_zpow, ht₁]
    have h2 : t * z₁ ^ m * t⁻¹ = (z₁ ^ m)⁻¹ := by rw [← hn, ← conj_zpow, ht₂, inv_zpow]
    have hww : z₁ ^ m * z₁ ^ m = 1 := by
      calc z₁ ^ m * z₁ ^ m = (z₁ ^ m)⁻¹ * z₁ ^ m := by rw [← h2, h1]
        _ = 1 := inv_mul_cancel _
    have h2' : orderOf (z₁ ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hww)
    have hp' : orderOf (z₁ ^ m) ∣ p := hz₁ ▸ orderOf_dvd_of_mem_zpowers hw1
    have h1' : orderOf (z₁ ^ m) ∣ Nat.gcd 2 p := Nat.dvd_gcd h2' hp'
    rw [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one] at h1'
    exact mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1'))
  have hcomm : zpowers z₁ ⊔ zpowers z₂ ≤
      centralizer ((zpowers z₁ ⊔ zpowers z₂ : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_ <;> rw [← le_centralizer_iff]
    · exact sup_le (hc (Commute.refl z₁)) (hc h12)
    · exact sup_le (hc h12.symm) (hc (Commute.refl z₂))
  set E := zpowers z₁ ⊔ zpowers z₂ with hE
  let S : Subgroup G :=
    { carrier := {x | x ∈ E ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (mem_centralizer_iff.mp (hcomm hb.1) a ha.1) p), ha.2, hb.2,
          one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hES : E ≤ S := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · exact ⟨mem_sup_left (mem_zpowers z₁), by rw [← hz₁, pow_orderOf_eq_one]⟩
    · exact ⟨mem_sup_right (mem_zpowers z₂), by rw [← hz₂, pow_orderOf_eq_one]⟩
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (hES hx).2⟩, ?_⟩
  · exact mem_centralizer_iff.mp (hcomm b.2) a a.2
  · rw [hE, CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hN12 H12, Nat.card_zpowers,
      Nat.card_zpowers, hz₁, hz₂, sq]

theorem isElemAbelian_zpowers_sup_zpowers_sup_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z₁ z₂ z₃ t₁ t₃ : G} (h12 : Commute z₁ z₂) (h13 : Commute z₁ z₃) (h23 : Commute z₂ z₃)
    (hz₁ : orderOf z₁ = p) (hz₂ : orderOf z₂ = p) (hz₃ : orderOf z₃ = p)
    (ht₁₁ : t₁ * z₁ * t₁⁻¹ = z₁) (ht₁₂ : t₁ * z₂ * t₁⁻¹ = z₂⁻¹)
    (ht₃₃ : t₃ * z₃ * t₃⁻¹ = z₃) (ht₃₁ : t₃ * z₁ * t₃⁻¹ = z₁⁻¹) (ht₃₂ : t₃ * z₂ * t₃⁻¹ = z₂⁻¹) :
    CFSG.Open.IsElemAbelian p (zpowers z₁ ⊔ zpowers z₂ ⊔ zpowers z₃) ∧
      Nat.card (zpowers z₁ ⊔ zpowers z₂ ⊔ zpowers z₃ : Subgroup G) = p ^ 3 := by
  have key : ∀ {z w t : G}, orderOf z = p → w ∈ zpowers z → t * w * t⁻¹ = w →
      t * w * t⁻¹ = w⁻¹ → w = 1 := by
    intro z w t hz hw h1 h2
    have hww : w * w = 1 := by
      have : w = w⁻¹ := h1.symm.trans h2
      calc w * w = w⁻¹ * w := by rw [← this]
        _ = 1 := inv_mul_cancel w
    have h2' : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hww)
    have hp' : orderOf w ∣ p := hz ▸ orderOf_dvd_of_mem_zpowers hw
    have h1' : orderOf w ∣ Nat.gcd 2 p := Nat.dvd_gcd h2' hp'
    rw [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one] at h1'
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1')
  have powfix : ∀ {t z : G}, t * z * t⁻¹ = z → ∀ w ∈ zpowers z, t * w * t⁻¹ = w := by
    intro t z h w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow, h]
  have powinv : ∀ {t z : G}, t * z * t⁻¹ = z⁻¹ → ∀ w ∈ zpowers z, t * w * t⁻¹ = w⁻¹ := by
    intro t z h w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow, h, inv_zpow]
  have hc : ∀ {a b : G}, Commute a b → zpowers b ≤ centralizer (zpowers a : Set G) := by
    intro a b hab
    rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
    exact (hab.zpow_left n).eq
  have hN12 : zpowers z₂ ≤ normalizer ((zpowers z₁ : Subgroup G) : Set G) :=
    (hc h12).trans (centralizer_le_normalizer _)
  have H12 : zpowers z₁ ⊓ zpowers z₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    exact mem_bot.mpr (key hz₂ hw2 (powfix ht₁₁ w hw1) (powinv ht₁₂ w hw2))
  have hcard12 : Nat.card (zpowers z₁ ⊔ zpowers z₂ : Subgroup G) = p * p := by
    rw [CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hN12 H12, Nat.card_zpowers, Nat.card_zpowers,
      hz₁, hz₂]
  have hinv12 : ∀ w ∈ zpowers z₁ ⊔ zpowers z₂, t₃ * w * t₃⁻¹ = w⁻¹ := by
    intro w hw
    have hw' : w ∈ ((zpowers z₁ ⊔ zpowers z₂ : Subgroup G) : Set G) := hw
    rw [coe_mul_of_right_le_normalizer_left _ _ hN12] at hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    have hab : a * b = b * a := mem_centralizer_iff.mp (hc h12 hb) a ha
    calc t₃ * (a * b) * t₃⁻¹ = (t₃ * a * t₃⁻¹) * (t₃ * b * t₃⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [powinv ht₃₁ a ha, powinv ht₃₂ b hb]
      _ = (a * b)⁻¹ := by rw [hab, mul_inv_rev]
  have H3 : (zpowers z₁ ⊔ zpowers z₂) ⊓ zpowers z₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw12, hw3⟩
    exact mem_bot.mpr (key hz₃ hw3 (powfix ht₃₃ w hw3) (hinv12 w hw12))
  have hC3 : zpowers z₁ ⊔ zpowers z₂ ≤ centralizer (zpowers z₃ : Set G) :=
    sup_le (hc h13.symm) (hc h23.symm)
  have hN3 : zpowers z₃ ≤ normalizer ((zpowers z₁ ⊔ zpowers z₂ : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp hC3).trans (centralizer_le_normalizer _)
  have hcomm : zpowers z₁ ⊔ zpowers z₂ ⊔ zpowers z₃ ≤
      centralizer ((zpowers z₁ ⊔ zpowers z₂ ⊔ zpowers z₃ : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [← le_centralizer_iff]
    · exact sup_le (sup_le (hc (Commute.refl z₁)) (hc h12)) (hc h13)
    · exact sup_le (sup_le (hc h12.symm) (hc (Commute.refl z₂))) (hc h23)
    · exact sup_le (sup_le (hc h13.symm) (hc h23.symm)) (hc (Commute.refl z₃))
  set E := zpowers z₁ ⊔ zpowers z₂ ⊔ zpowers z₃ with hE
  let S : Subgroup G :=
    { carrier := {x | x ∈ E ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (mem_centralizer_iff.mp (hcomm hb.1) a ha.1) p), ha.2, hb.2,
          one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hES : E ≤ S := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le]
    · exact ⟨mem_sup_left (mem_sup_left (mem_zpowers z₁)), by rw [← hz₁, pow_orderOf_eq_one]⟩
    · exact ⟨mem_sup_left (mem_sup_right (mem_zpowers z₂)), by rw [← hz₂, pow_orderOf_eq_one]⟩
    · exact ⟨mem_sup_right (mem_zpowers z₃), by rw [← hz₃, pow_orderOf_eq_one]⟩
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (hES hx).2⟩, ?_⟩
  · exact mem_centralizer_iff.mp (hcomm b.2) a a.2
  · rw [hE, CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hN3 H3, hcard12, Nat.card_zpowers, hz₃]
    ring

theorem exists_minimal_not_le_centralizer [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {T B : Subgroup G} (hT : IsPGroup p T) (hB : IsKleinFour B)
    (hBT : B ≤ normalizer (T : Set G)) {u : G} (huB : u ∈ normalizer (B : Set G))
    (huT : u ∈ normalizer (T : Set G)) (hTB : ¬ T ≤ centralizer (B : Set G)) :
    ∃ D : Subgroup G, D ≤ T ∧ B ≤ normalizer (D : Set G) ∧ u ∈ normalizer (D : Set G) ∧
      ¬ D ≤ centralizer (B : Set G) ∧ ⁅D, D⁆ ≤ centralizer (B : Set G) ∧ ⁅D, ⁅D, D⁆⁆ = ⊥ := by
  classical
  obtain ⟨D, ⟨hDT, hBD, huD, hDB⟩, hmin⟩ :=
    Set.Finite.exists_minimalFor (fun D : Subgroup G => Nat.card D)
      {D : Subgroup G | D ≤ T ∧ B ≤ normalizer (D : Set G) ∧ u ∈ normalizer (D : Set G) ∧
        ¬ D ≤ centralizer (B : Set G)} (Set.toFinite _) ⟨T, le_rfl, hBT, huT, hTB⟩
  have hDp : IsPGroup p D := hT.to_le hDT
  have hDodd : Odd (Nat.card D) := by
    obtain ⟨k, hk⟩ := hDp.exists_card_eq
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hmin' : ∀ D' : Subgroup G, D' ≤ D → B ≤ normalizer (D' : Set G) →
      u ∈ normalizer (D' : Set G) → ¬ D' ≤ centralizer (B : Set G) → D' = D := by
    intro D' hD'D hBD' huD' hD'B
    exact eq_of_le_of_card_ge hD'D (hmin ⟨hD'D.trans hDT, hBD', huD', hD'B⟩ (card_le_of_le hD'D))
  have hDD : ⁅D, D⁆ ≤ centralizer (B : Set G) := by
    by_contra h
    have heq := hmin' _ (commutator_le_left_of_le_normalizer le_normalizer)
      (fun b hb => mem_normalizer_commutator (hBD hb) (hBD hb))
      (mem_normalizer_commutator huD huD) h
    exact commutator_ne_self_of_isPGroup hDp (fun h' => hDB (h' ▸ bot_le)) heq
  have hDBc : ⁅D, B⁆ = D := by
    refine hmin' _ (commutator_le_left_of_le_normalizer hBD)
      (fun b hb => mem_normalizer_commutator (hBD hb) (le_normalizer hb))
      (mem_normalizer_commutator huD huB) fun h => hDB ?_
    rw [← commutator_eq_bot_iff_le_centralizer] at h ⊢
    rwa [commutator_commutator_eq_of_isKleinFour hB hDodd hBD] at h
  refine ⟨D, hDT, hBD, huD, hDB, hDD, ?_⟩
  have h3 : ⁅⁅D, B⁆, ⁅D, D⁆⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · have : ⁅B, ⁅D, D⁆⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        exact le_centralizer_iff.mp hDD
      rw [this, commutator_bot_left]
    · rw [commutator_eq_bot_iff_le_centralizer]
      exact (commutator_le_left_of_le_normalizer fun d hd =>
        mem_normalizer_commutator (le_normalizer hd) (le_normalizer hd)).trans hDD
  rwa [hDBc] at h3

theorem exists_isElemAbelian_card_eq_pow_three [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T B : Subgroup G} (hT : IsPGroup p T) (hB : IsKleinFour B)
    (hBT : B ≤ normalizer (T : Set G)) {u : G} (huB : u ∈ normalizer (B : Set G))
    (huT : u ∈ normalizer (T : Set G)) (hfix : ∀ b ∈ B, b ≠ 1 → u * b * u⁻¹ ≠ b)
    (hTB : ¬ T ≤ centralizer (B : Set G)) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDT, hBD, huD, hDB, hDD, hDDD⟩ :=
    exists_minimal_not_le_centralizer hp2 hT hB hBT huB huT hTB
  have hDp : IsPGroup p D := hT.to_le hDT
  have hDodd : Odd (Nat.card D) := by
    obtain ⟨k, hk⟩ := hDp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨b, hb, hb1, x, hxD, hx1, hbx, hx⟩ :=
    exists_fixed_inverted_of_isKleinFour hB hDodd hBD hDB
  obtain ⟨hbx₂, hx₂⟩ := conj_fixed_inverted huB hbx hx
  obtain ⟨hbx₃, hx₃⟩ := conj_fixed_inverted huB hbx₂ hx₂
  have hconj_mem : ∀ {K : Subgroup G} {g : G}, u ∈ normalizer (K : Set G) → g ∈ K →
      u * g * u⁻¹ ∈ K := fun hu hg => (mem_normalizer_iff.mp hu _).mp hg
  have hconj_ne : ∀ {g : G}, g ≠ 1 → u * g * u⁻¹ ≠ 1 := fun {g} hg h => hg (by
    have := congrArg (fun z => u⁻¹ * z * u) h
    simpa [mul_assoc] using this)
  have hb₂ := hconj_mem huB hb
  have hb₃ := hconj_mem huB hb₂
  have hb₂1 := hconj_ne hb1
  have hb₃1 := hconj_ne hb₂1
  have hx₂D := hconj_mem huD hxD
  have hx₃D := hconj_mem huD hx₂D
  have hx₂1 := hconj_ne hx1
  have hx₃1 := hconj_ne hx₂1
  have hb₃eq : u * (u * b * u⁻¹) * u⁻¹ = b * (u * b * u⁻¹) :=
    conj_conj_eq_mul_of_fixedPointFree hB huB hfix hb hb1
  have hbb₂ : u * b * u⁻¹ ≠ b := hfix b hb hb1
  have hnot : ∀ {c d : G}, d ∈ B → d ≠ 1 → c ≠ 1 → c ≠ d → c ∉ zpowers d :=
      fun hd hd1 hc1 hcd h => by
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hB hd hd1) h with h | h
    · exact hc1 h
    · exact hcd h
  have hbz₂ : b ∉ zpowers (u * b * u⁻¹) := hnot hb₂ hb₂1 hb1 hbb₂.symm
  have hbz₃ : b ∉ zpowers (u * (u * b * u⁻¹) * u⁻¹) := by
    refine hnot hb₃ hb₃1 hb1 ?_
    rw [hb₃eq]
    intro h
    exact hb₂1 (by simpa using h.symm)
  have hb₂z₃ : u * b * u⁻¹ ∉ zpowers (u * (u * b * u⁻¹) * u⁻¹) := by
    refine hnot hb₃ hb₃1 hb₂1 ?_
    rw [hb₃eq]
    intro h
    exact hb1 (by simpa using h.symm)
  have hb₃z : u * (u * b * u⁻¹) * u⁻¹ ∉ zpowers b := by
    refine hnot hb hb1 hb₃1 ?_
    rw [hb₃eq]
    intro h
    exact hb₂1 (by simpa using h)
  have hb₃z₂ : u * (u * b * u⁻¹) * u⁻¹ ∉ zpowers (u * b * u⁻¹) := by
    refine hnot hb₂ hb₂1 hb₃1 ?_
    rw [hb₃eq]
    intro h
    exact hb1 (by simpa using h)
  have c12 := mul_comm_of_conj_eq_of_conj_eq_inv hDodd hDD hDDD hb hxD hx₂D hbx
    (hx₂ b hb hbz₂)
  have c13 := mul_comm_of_conj_eq_of_conj_eq_inv hDodd hDD hDDD hb hxD hx₃D hbx
    (hx₃ b hb hbz₃)
  have c23 := mul_comm_of_conj_eq_of_conj_eq_inv hDodd hDD hDDD hb₂ hx₂D hx₃D hbx₂
    (hx₃ _ hb₂ hb₂z₃)
  have hpdvd : ∀ {y : G}, y ∈ D → y ≠ 1 → p ∣ orderOf y := by
    intro y hy hy1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hDp) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hy1
    · exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hord : ∀ {y : G}, y ∈ D → y ≠ 1 → orderOf (y ^ (orderOf y / p)) = p := fun hy hy1 =>
    orderOf_pow_orderOf_div (orderOf_pos _).ne' (hpdvd hy hy1)
  have pfix : ∀ {t y : G} (m : ℕ), t * y * t⁻¹ = y → t * y ^ m * t⁻¹ = y ^ m := by
    intro t y m h
    rw [← conj_pow, h]
  have pinv : ∀ {t y : G} (m : ℕ), t * y * t⁻¹ = y⁻¹ → t * y ^ m * t⁻¹ = (y ^ m)⁻¹ := by
    intro t y m h
    rw [← conj_pow, h, inv_pow]
  obtain ⟨hE, hcard⟩ := isElemAbelian_zpowers_sup_zpowers_sup_zpowers hp hp2
    ((Commute.pow_pow c12 _ _)) ((Commute.pow_pow c13 _ _)) ((Commute.pow_pow c23 _ _))
    (hord hxD hx1) (hord hx₂D hx₂1) (hord hx₃D hx₃1)
    (pfix _ hbx) (pinv _ (hx₂ b hb hbz₂))
    (pfix _ hbx₃) (pinv _ (hx _ hb₃ hb₃z)) (pinv _ (hx₂ _ hb₃ hb₃z₂))
  refine ⟨_, ?_, hE, hcard⟩
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le]
  · exact hDT (pow_mem hxD _)
  · exact hDT (pow_mem hx₂D _)
  · exact hDT (pow_mem hx₃D _)

theorem exists_isElemAbelian_card_eq_sq [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T B : Subgroup G} (hT : IsPGroup p T) (hB : IsKleinFour B)
    (hBT : B ≤ normalizer (T : Set G)) (hTB : ∀ b ∈ B, b ≠ 1 → ¬ T ≤ C b) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hTodd : Odd (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨b₀, hb₀, -, -, hb₀o, -⟩ := exists_eq_zpowers_sup_zpowers hB
  have hb₀1 : b₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hb₀o
    norm_num at hb₀o
  have hTC : ¬ T ≤ centralizer (B : Set G) := fun h =>
    hTB b₀ hb₀ hb₀1 (h.trans (centralizer_le (Set.singleton_subset_iff.mpr hb₀)))
  set Z := T ⊓ centralizer (T : Set G) with hZ
  have hBZ : B ≤ normalizer (Z : Set G) := fun b hb => inf_normalizer_le_normalizer_inf
    ⟨hBT hb, mem_normalizer_centralizer_of_mem_normalizer (hBT hb)⟩
  have hZodd : Odd (Nat.card Z) := hTodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    have hT1 : T ≠ ⊥ := fun h => hTC (h ▸ bot_le)
    have : Nontrivial T := (nontrivial_iff_ne_bot T).mpr hT1
    have := hT.center_nontrivial
    obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : center T)
    refine ⟨c, ⟨c.2, mem_centralizer_iff.mpr fun t ht => ?_⟩, fun h => hc1 ?_⟩
    · exact congrArg Subtype.val (mem_center_iff.mp hc ⟨t, ht⟩)
    · exact Subtype.ext (Subtype.ext h)
  obtain ⟨t, a, a', haT, ha1, ha'T, ha'1, hcomm, hta, hta'⟩ : ∃ t a a' : G, a ∈ T ∧ a ≠ 1 ∧
      a' ∈ T ∧ a' ≠ 1 ∧ Commute a a' ∧ t * a * t⁻¹ = a ∧ t * a' * t⁻¹ = a'⁻¹ := by
    by_cases hZB : Z ≤ centralizer (B : Set G)
    · obtain ⟨b, hb, hb1, x, hxT, hx1, -, hx⟩ :=
        exists_fixed_inverted_of_isKleinFour hB hTodd hBT hTC
      obtain ⟨s, hs, hsb⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hB hb hb1
      refine ⟨s, z₀, x, hz₀Z.1, hz₀1, hxT, hx1, ?_, ?_, hx s hs hsb⟩
      · exact (mem_centralizer_iff.mp hz₀Z.2 x hxT).symm
      · rw [mem_centralizer_iff.mp (hZB hz₀Z) s hs, mul_inv_cancel_right]
    · obtain ⟨c, hc, hc1, z, hzZ, hz1, -, hz⟩ :=
        exists_fixed_inverted_of_isKleinFour hB hZodd hBZ hZB
      obtain ⟨b, hb, hb1, hcb, x, hxT, hx1, hbx, -⟩ :=
        exists_fixed_inverted_of_not_le_C hB hTodd hBT hc (hTB c hc hc1)
      have hbc : b ∉ zpowers c := by
        intro h
        rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hB hc hc1) h with
          h | h
        · exact hb1 h
        · exact hcb (by rw [← h]; exact mem_zpowers b)
      refine ⟨b, x, z, hxT, hx1, hzZ.1, hz1, ?_, hbx, hz b hb hbc⟩
      exact mem_centralizer_iff.mp hzZ.2 x hxT
  have hpdvd : ∀ {y : G}, y ∈ T → y ≠ 1 → p ∣ orderOf y := by
    intro y hy hy1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hy1
    · exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hord : ∀ {y : G}, y ∈ T → y ≠ 1 → orderOf (y ^ (orderOf y / p)) = p := fun hy hy1 =>
    orderOf_pow_orderOf_div (orderOf_pos _).ne' (hpdvd hy hy1)
  obtain ⟨hE, hcard⟩ := isElemAbelian_zpowers_sup_zpowers hp hp2 (t := t)
    (Commute.pow_pow hcomm _ _) (hord haT ha1) (hord ha'T ha'1) (by rw [← conj_pow, hta])
    (by rw [← conj_pow, hta', inv_pow])
  refine ⟨_, sup_le ?_ ?_, hE, hcard⟩ <;> rw [zpowers_le]
  · exact pow_mem haT _
  · exact pow_mem ha'T _

end FourGroup

section Lemma59

variable {G : Type} [Group G]

theorem pow_eq_one_of_mul_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R' W : Subgroup G}
    [IsCyclic W] (hWp : IsPGroup p W) (hR'W : R' ≤ normalizer (W : Set G)) (hRW : R' ⊓ W = ⊥)
    {r w : G} (hr : r ∈ R') (hw : w ∈ W) (h : (r * w) ^ p = 1) : w ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hrW : r⁻¹ ∈ normalizer (W : Set G) := inv_mem (hR'W hr)
  let σ : W →* W :=
    { toFun := fun v => ⟨r⁻¹ * v * r⁻¹⁻¹, (mem_normalizer_iff.mp hrW v).mp v.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have hσ : ∀ v ∈ W, r⁻¹ * v * r = v ^ m := fun v hv => by
    have := congrArg Subtype.val (hm ⟨v, hv⟩)
    simpa [σ] using this
  let S : ℕ → ℤ := fun k => Nat.rec 0 (fun _ s => m * s + 1) k
  have hSs : ∀ k, S (k + 1) = m * S k + 1 := fun k => rfl
  have hpow : ∀ k : ℕ, (r * w) ^ k = r ^ k * w ^ (S k) := by
    intro k
    induction k with
    | zero => simp [S]
    | succ k ih =>
      have h1 : r⁻¹ * w ^ S k * r = w ^ (S k * m) := by
        rw [hσ _ (zpow_mem hw _), ← zpow_mul]
      calc (r * w) ^ (k + 1) = r ^ k * w ^ S k * (r * w) := by rw [pow_succ, ih]
        _ = r ^ k * r * (r⁻¹ * w ^ S k * r) * w := by group
        _ = r ^ (k + 1) * w ^ (S (k + 1)) := by
          rw [h1, hSs, ← pow_succ, mul_comm m, zpow_add_one, mul_assoc]
  have h1 : r ^ p * w ^ S p = 1 := by rw [← hpow, h]
  have hrp : r ^ p ∈ R' ⊓ W := by
    refine ⟨pow_mem hr p, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact W.inv_mem (W.zpow_mem hw _)
  rw [hRW, mem_bot] at hrp
  have hwS : w ^ S p = 1 := by rwa [hrp, one_mul] at h1
  by_cases hw1 : w = 1
  · rw [hw1, one_pow]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hWp) ⟨w, hw⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hw1 hj
  have hconj : ∀ k : ℕ, r⁻¹ ^ k * w * r ^ k = w ^ (m ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc r⁻¹ ^ (k + 1) * w * r ^ (k + 1) = r⁻¹ * (r⁻¹ ^ k * w * r ^ k) * r := by
            rw [pow_succ', pow_succ]; group
        _ = r⁻¹ * w ^ (m ^ k) * r := by rw [ih]
        _ = (w ^ (m ^ k)) ^ m := hσ _ (zpow_mem hw _)
        _ = w ^ (m ^ (k + 1)) := by rw [← zpow_mul, pow_succ]
  have hmp : w ^ (m ^ p) = w := by
    rw [← hconj p, inv_pow, hrp, inv_one, one_mul, mul_one]
  have hdvd : ((orderOf w : ℕ) : ℤ) ∣ m ^ p - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hmp, zpow_one, mul_inv_cancel]
  have hpdvd : (p : ℤ) ∣ m ^ p - 1 := by
    refine dvd_trans ?_ hdvd
    rw [hj]
    exact_mod_cast dvd_pow_self p hj0
  have hferm : (p : ℤ) ∣ m ^ p - m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  obtain ⟨e, he⟩ : (p : ℤ) ∣ m - 1 := by
    have := dvd_sub hpdvd hferm
    rwa [show m ^ p - 1 - (m ^ p - m) = m - 1 by ring] at this
  have hSmod : ∀ k : ℕ, ((p : ℤ) ^ 2) ∣ 2 * S k - 2 * k - (m - 1) * k * (k - 1) := by
    intro k
    induction k with
    | zero => simp [S]
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨e ^ 2 * k * (k - 1) + m * t, ?_⟩
      rw [hSs]
      push_cast
      linear_combination m * ht + ((k : ℤ) * (k - 1) * (m - 1 + p * e)) * he
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have hS2 : ((p : ℤ) ^ 2) ∣ S p := by
      have h3 : ((orderOf w : ℕ) : ℤ) ∣ S p := orderOf_dvd_iff_zpow_eq_one.mpr hwS
      rw [hj] at h3
      refine dvd_trans ?_ h3
      exact_mod_cast pow_dvd_pow p (by omega)
    obtain ⟨t, ht⟩ := hSmod p
    obtain ⟨s, hs⟩ := hS2
    have h4 : ((p : ℤ) ^ 2) ∣ 2 * p := ⟨2 * s - t - e * (p - 1), by
      linear_combination -ht + 2 * hs - ((p : ℤ) * (p - 1)) * he⟩
    have h5 : (p : ℤ) ∣ 2 := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      obtain ⟨c, hc⟩ := h4
      exact ⟨c, by
        have := mul_left_cancel₀ hp0 (show (p : ℤ) * 2 = p * (p * c) by
          rw [mul_comm (p : ℤ) 2, hc]; ring)
        rw [this]⟩
    have h6 : p ∣ 2 := by exact_mod_cast h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h6)
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact pow_dvd_pow p hj1 |>.trans (by rw [pow_one])

theorem mul_comm_of_conj_eq_inv_of_conj_eq {t g e : G} (hg : Odd (orderOf g))
    (htg : t * g * t⁻¹ = g⁻¹) (hte : t * e * t⁻¹ = e)
    (htge : t * (g * e * g⁻¹) * t⁻¹ = g * e * g⁻¹) : g * e = e * g := by
  have h1 : g * e * g⁻¹ = g⁻¹ * e * g := by
    rw [← htge]
    calc t * (g * e * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * (t * e * t⁻¹) * (t * g * t⁻¹)⁻¹ := by group
      _ = g⁻¹ * e * g := by rw [htg, hte, inv_inv]
  have h2 : Commute (g ^ 2) e := by
    change g ^ 2 * e = e * g ^ 2
    calc g ^ 2 * e = g * (g * e * g⁻¹) * g := by rw [sq]; group
      _ = g * (g⁻¹ * e * g) * g := by rw [h1]
      _ = e * g ^ 2 := by rw [sq]; group
  obtain ⟨k, hk⟩ := hg
  have h3 : (g ^ 2) ^ (k + 1) = g := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have := (h2.pow_left (k + 1)).eq
  rwa [h3] at this

theorem exists_mem_not_mem_conj_eq_inv [Finite G] {A N M : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hN : Odd (Nat.card N))
    (hAN : A ≤ normalizer (N : Set G)) (hNM : ¬ N ≤ M) {t : G} (ht : t ∈ A)
    (htM : N ⊓ C t ≤ M) :
    ∃ g ∈ N, g ∉ M ∧ t * g * t⁻¹ = g⁻¹ ∧ ∀ a ∈ A, a * g * a⁻¹ = g ∨ a * g * a⁻¹ = g⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hNM fun n hn => htM ⟨hn, mem_centralizer_singleton_iff.mpr (by group)⟩
  have : Nontrivial A := ⟨⟨⟨t, ht⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  have : CFSG.IsElementaryAbelian 2 A :=
    { is_comm := hA.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hA.2 a a.2) }
  have htt : t * t = 1 := by rw [← sq]; exact hA.2 t ht
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  let : MulDistribMulAction A N := Subgroup.conjMulDistribMulActionOfLeNormalizer A N hAN
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := N)
    (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h))
  obtain ⟨B, hB2, hBM⟩ : ∃ B : Subgroup A, B.index = 2 ∧
      ¬ CFSG.fixedPointSubgroup B N ≤ M.subgroupOf N := by
    by_contra hcon
    push Not at hcon
    apply hNM
    intro n hn
    have h1 : (⟨n, hn⟩ : N) ∈
        ⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B N := by
      rw [hgen]
      exact mem_top _
    exact (iSup₂_le fun B hB => hcon B hB) h1
  obtain ⟨⟨g₀, hg₀N⟩, hg₀B, hg₀M⟩ := SetLike.not_le_iff_exists.mp hBM
  rw [mem_subgroupOf] at hg₀M
  have hfix : ∀ b ∈ B, ((b : A) : G) * g₀ * ((b : A) : G)⁻¹ = g₀ := fun b hb =>
    congrArg Subtype.val (hg₀B ⟨b, hb⟩)
  set B' : Subgroup G := B.map A.subtype with hB'
  have hB'A : B' ≤ A := map_subtype_le B
  have hmemB' : ∀ {a : G} (ha : a ∈ A), (⟨a, ha⟩ : A) ∈ B → a ∈ B' := fun ha h => ⟨_, h, rfl⟩
  have htB : (⟨t, ht⟩ : A) ∉ B := by
    intro h
    exact hg₀M (htM ⟨hg₀N, mem_centralizer_singleton_iff.mpr (by
      calc g₀ * t = t * g₀ * t⁻¹ * t := by rw [hfix _ h]
        _ = t * g₀ := by group)⟩)
  set T : Subgroup G := N ⊓ centralizer (B' : Set G) with hT
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have htC : t ∈ centralizer (B' : Set G) := mem_centralizer_iff.mpr fun b hb =>
    hcomm b (hB'A hb) t ht
  have htT : t ∈ normalizer (T : Set G) := inf_normalizer_le_normalizer_inf
    ⟨hAN ht, mem_normalizer_centralizer_of_mem_normalizer (centralizer_le_normalizer _ htC)⟩
  have hTodd : Odd (Nat.card T) := hN.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hg₀T : g₀ ∈ T := by
    refine ⟨hg₀N, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    calc (b : G) * g₀ = (b : G) * g₀ * (b : G)⁻¹ * b := by group
      _ = g₀ * b := by rw [hfix b hb]
  obtain ⟨⟨c, g⟩, ⟨hc, hg⟩, hcg⟩ :=
    (OddInversion.odd_involution_product_decomposition hTodd ht2 htT).1.surjOn hg₀T
  simp only at hcg
  have hgT : g ∈ T := hg.1
  have hg₀M' : g₀ ∉ M := hg₀M
  have hgM : g ∉ M := by
    intro h
    apply hg₀M'
    rw [← hcg]
    exact mul_mem (htM ⟨hc.1.1, hc.2⟩) h
  have htg : t * g * t⁻¹ = g⁻¹ := hg.2
  refine ⟨g, hgT.1, hgM, htg, fun a ha => ?_⟩
  have hgC : ∀ b ∈ B', b * g * b⁻¹ = g := fun b hb => by
    rw [mem_centralizer_iff.mp hgT.2 b hb, mul_inv_cancel_right]
  by_cases haB : (⟨a, ha⟩ : A) ∈ B
  · exact Or.inl (hgC a (hmemB' ha haB))
  · right
    have hat : (⟨a, ha⟩ : A) * ⟨t, ht⟩ ∈ B :=
      (mul_mem_iff_of_index_two hB2).mpr (iff_of_false haB htB)
    have h1 := hgC (a * t) (hmemB' (mul_mem ha ht) hat)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have htg' : t⁻¹ * g * t = g⁻¹ := by
      calc t⁻¹ * g * t = t * g * t⁻¹ := by rw [htinv]
        _ = g⁻¹ := htg
    calc a * g * a⁻¹ = (a * t) * (t⁻¹ * g * t) * (a * t)⁻¹ := by group
      _ = ((a * t) * g * (a * t)⁻¹)⁻¹ := by rw [htg']; group
      _ = g⁻¹ := by rw [h1]

theorem exists_le_card_le_of_isCyclic [Finite G] {p : ℕ} (hp : 0 < p) {W : Subgroup G}
    [IsCyclic W] : ∃ W₁ : Subgroup G, W₁ ≤ W ∧ Nat.card W₁ ≤ p ∧
      (∀ w ∈ W, w ^ p = 1 → w ∈ W₁) ∧ normalizer (W : Set G) ≤ normalizer (W₁ : Set G) := by
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let W₁ : Subgroup G :=
    { carrier := {w | w ∈ W ∧ w ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hcomm a ha.1 b hb.1) p, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hW₁W : W₁ ≤ W := fun w hw => hw.1
  refine ⟨W₁, hW₁W, ?_, fun w hw hwp => ⟨hw, hwp⟩, fun a ha => ?_⟩
  · have : IsCyclic W₁ := Subgroup.isCyclic_of_le hW₁W
    obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := W₁)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hy]
    refine Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one ?_)
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact y.2.2
  · refine mem_normalizer_fintype fun w hw =>
      ⟨(mem_normalizer_iff.mp ha w).mp hw.1, ?_⟩
    rw [conj_pow, hw.2, mul_one, mul_inv_cancel]

theorem card_le_mul_card_inf_of_le_sup [Finite G] {p : ℕ} {Q₀ W₁ F : Subgroup G}
    (hN : Q₀ ≤ normalizer (W₁ : Set G)) (hi : W₁ ⊓ Q₀ = ⊥) (hW₁ : Nat.card W₁ ≤ p)
    (hF : F ≤ W₁ ⊔ Q₀) : Nat.card F ≤ p * Nat.card (Q₀ ⊓ F : Subgroup G) := by
  have h1 := relIndex_mul_card (H := Q₀) (K := F)
  have h2 := relIndex_mul_card (H := Q₀) (K := W₁ ⊔ Q₀)
  rw [inf_of_le_left (le_sup_right : Q₀ ≤ W₁ ⊔ Q₀),
    CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hN hi] at h2
  have h3 : Q₀.relIndex (W₁ ⊔ Q₀) = Nat.card W₁ := Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have h4 : Q₀.relIndex F ≤ Q₀.relIndex (W₁ ⊔ Q₀) :=
    relIndex_le_of_le_right hF (by rw [h3]; exact Nat.card_pos.ne')
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h4.trans (h3 ▸ hW₁))

end Lemma59

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem P_inf_centralizer_V_le_Pstar : 𝔨.P ⊓ centralizer (𝔨.V : Set G) ≤ 𝔨.Pstar :=
  fun _ hg => ⟨hg.1, 𝔨.K_eq_normalizer_V ▸ centralizer_le_normalizer _ hg.2⟩

theorem commutator_Pstar_Y_le_V : ⁅𝔨.Pstar, ρ.Y⁆ ≤ 𝔨.V := by
  rw [← 𝔨.Pstar_inf_O_K₁]
  exact le_inf (commutator_le_left_of_le_normalizer (ρ.Y_le_A.trans 𝔨.A_le_normalizer_Pstar))
    ((commutator_mono 𝔨.Pstar_le_K₁ le_rfl).trans 𝔨.hK₁q.1)

theorem lemma_5_7_of (Q : Subgroup G) (hQP : Q ≤ 𝔨.P) (hAQ : A ≤ normalizer (Q : Set G))
    (hPQ : 𝔨.P ≤ normalizer (Q : Set G)) (hQY : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ Q ≤ C y) :
    ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔨.V ≤ C y := by
  intro y hy hy1 hVy
  have : Fact p.Prime := ⟨𝔨.hp⟩
  have hyo : orderOf y = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_Y hy hy1
  have hyA : y ∈ A := ρ.Y_le_A hy
  have hyQ : y ∈ normalizer (Q : Set G) := hAQ hyA
  have hVP : 𝔨.V ≤ 𝔨.P := 𝔨.V_le_Pstar.trans 𝔨.Pstar_le_P
  have hVQ : 𝔨.V ≤ normalizer (Q : Set G) := hVP.trans hPQ
  have hnot : ¬ Q ⊓ centralizer (𝔨.V : Set G) ≤ centralizer (zpowers y : Set G) := by
    intro hfix
    have hle := CFSG.RankThree.PartTwo.Sec18.Item188Proof.centralizes_of_thompson_AxB
      (𝔨.isPGroup_of_le_P hQP)
      (by
        rw [Nat.card_zpowers, hyo]
        exact (Nat.coprime_two_left.mpr 𝔨.odd_p))
      (𝔨.isPGroup_of_le_P hVP) (zpowers_le.mpr hyQ) hVQ
      (by
        rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
        intro v hv
        exact (mem_centralizer_singleton_iff.mp (hVy hv)))
      hfix
    refine hQY y hy hy1 fun q hq => ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hle hq) y (mem_zpowers y)).symm
  have hEP : Q ⊓ centralizer (𝔨.V : Set G) ≤ 𝔨.Pstar :=
    (inf_le_inf_right _ hQP).trans 𝔨.P_inf_centralizer_V_le_Pstar
  have hyE : y ∈ normalizer ((Q ⊓ centralizer (𝔨.V : Set G) : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyQ,
      mem_normalizer_centralizer_of_mem_normalizer (𝔨.K_eq_normalizer_V ▸ 𝔨.A_le_K hyA)⟩
  have hFV : ⁅Q ⊓ centralizer (𝔨.V : Set G), zpowers y⁆ ≤ 𝔨.V :=
    (commutator_mono hEP (zpowers_le.mpr hy)).trans 𝔨.commutator_Pstar_Y_le_V
  apply hnot
  rw [← commutator_eq_bot_iff_le_centralizer]
  exact commutator_zpowers_eq_bot_of_le (𝔨.odd_card_of_le_P (inf_le_left.trans hQP)) hyo
    hyE hFV hVy

theorem U_le_R : 𝔨.U ≤ 𝔨.R := inf_le_left

theorem V_le_U : 𝔨.V ≤ 𝔨.U := by
  rw [𝔨.U_eq]
  refine le_inf 𝔨.V_le_Pstar fun v hv => ?_
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_iff.mp (𝔨.X_le_centralizer_V hx) v hv).symm

theorem U_le_Pstar : 𝔨.U ≤ 𝔨.Pstar := by
  rw [𝔨.U_eq]
  exact inf_le_left

theorem R_inf_Pstar : 𝔨.R ⊓ 𝔨.Pstar = 𝔨.U := by
  rw [𝔨.U_eq]
  change 𝔨.P ⊓ centralizer (ρ.X : Set G) ⊓ (𝔨.P ⊓ 𝔨.K) = 𝔨.P ⊓ 𝔨.K ⊓ centralizer (ρ.X : Set G)
  ext g
  simp only [mem_inf]
  tauto

theorem A_le_normalizer_U : A ≤ normalizer (𝔨.U : Set G) := by
  intro a ha
  rw [𝔨.U_eq]
  refine inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_Pstar ha, ?_⟩
  refine le_normalizer ?_
  rw [mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (ρ.hA.1.1.is_comm.comm ⟨x, ρ.X_le_A hx⟩ ⟨a, ha⟩)

theorem commutator_U_le_V : ⁅𝔨.U, 𝔨.U⁆ ≤ 𝔨.V := by
  obtain ⟨u, hu⟩ := 𝔨.hUV
  change 𝔨.U = 𝔨.V ⊔ zpowers u at hu
  have huU : u ∈ 𝔨.U := hu ▸ mem_sup_right (mem_zpowers u)
  have huV : zpowers u ≤ normalizer (𝔨.V : Set G) :=
    zpowers_le.mpr (𝔨.Pstar_le_normalizer_V (𝔨.U_le_Pstar huU))
  have hset : ((𝔨.U : Subgroup G) : Set G) = (𝔨.V : Set G) * (zpowers u : Set G) := by
    rw [hu]
    exact coe_mul_of_right_le_normalizer_left _ _ huV
  rw [commutator_le]
  intro a ha b hb
  have ha' : a ∈ ((𝔨.U : Subgroup G) : Set G) := ha
  have hb' : b ∈ ((𝔨.U : Subgroup G) : Set G) := hb
  rw [hset] at ha' hb'
  obtain ⟨v₁, hv₁, a₁, ha₁, rfl⟩ := Set.mem_mul.mp ha'
  obtain ⟨v₂, hv₂, b₁, hb₁, rfl⟩ := Set.mem_mul.mp hb'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₁
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb₁
  have hc : ⁅v₁ * u ^ i, v₂ * u ^ j⁆ =
      v₁ * (u ^ i * v₂ * (u ^ i)⁻¹) * (u ^ j * v₁⁻¹ * (u ^ j)⁻¹) * v₂⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hc]
  have h1 := (mem_normalizer_iff.mp (huV (zpow_mem (mem_zpowers u) i)) v₂).mp hv₂
  have h2 := (mem_normalizer_iff.mp (huV (zpow_mem (mem_zpowers u) j)) v₁⁻¹).mp (inv_mem hv₁)
  exact mul_mem (mul_mem (mul_mem hv₁ h1) h2) (inv_mem hv₂)

theorem Y_le_normalizer_R : ρ.Y ≤ normalizer (𝔨.R : Set G) := fun _ hy =>
  inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_P (ρ.Y_le_A hy),
    le_normalizer (ρ.Y_le_centralizer_X hy)⟩

theorem lemma_5_8_of (Q : Subgroup G) (hQP : Q ≤ 𝔨.P) (hAQ : A ≤ normalizer (Q : Set G))
    (hPQ : 𝔨.P ≤ normalizer (Q : Set G)) (hQY : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ Q ≤ C y)
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀) :
    𝔨.R = 𝔨.U := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  refine eq_of_inf_normalizer_le (𝔨.isPGroup_of_le_P inf_le_left) 𝔨.U_le_R ?_
  by_cases hU' : ⁅𝔨.U, 𝔨.U⁆ = ⊥
  ·
    have hUab : ∀ a ∈ 𝔨.U, ∀ b ∈ 𝔨.U, a * b = b * a := fun a ha b hb => by
      have h := commutator_mem_commutator ha hb
      rwa [hU', mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    have hT : Odd (Nat.card (𝔨.R ⊓ normalizer (𝔨.U : Set G) : Subgroup G)) :=
      𝔨.odd_card_of_le_P (inf_le_left.trans inf_le_left)
    have hYT : ρ.Y ≤ normalizer ((𝔨.R ⊓ normalizer (𝔨.U : Set G) : Subgroup G) : Set G) :=
      fun y hy => inf_normalizer_le_normalizer_inf ⟨𝔨.Y_le_normalizer_R hy,
        le_normalizer (𝔨.A_le_normalizer_U (ρ.Y_le_A hy))⟩
    refine le_of_forall_inf_C_le_of_isKleinFour ρ.isKleinFour_Y hT hYT fun y hy hy1 => ?_
    have hWU : ⁅𝔨.U, zpowers y⁆ ≤ 𝔨.U :=
      commutator_zpowers_le_of_mem_normalizer (𝔨.A_le_normalizer_U (ρ.Y_le_A hy))
    have hWV : ⁅𝔨.U, zpowers y⁆ ≤ 𝔨.V :=
      (commutator_mono 𝔨.U_le_Pstar (zpowers_le.mpr hy)).trans 𝔨.commutator_Pstar_Y_le_V
    have hW1 : ⁅𝔨.U, zpowers y⁆ ≠ ⊥ := by
      intro hW
      refine 𝔨.lemma_5_7_of Q hQP hAQ hPQ hQY y hy hy1 fun v hv => ?_
      have h := commutator_mem_commutator (𝔨.V_le_U hv) (mem_zpowers y)
      rw [hW, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact mem_centralizer_singleton_iff.mpr h
    have hyc : ∀ a ∈ A, a * y = y * a := fun a ha =>
      congrArg Subtype.val (ρ.hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨y, ρ.Y_le_A hy⟩)
    have hAW : A ≤ normalizer ((⁅𝔨.U, zpowers y⁆ : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_commutator_zpowers (𝔨.A_le_normalizer_U ha) (hyc a ha)
    have hUW : 𝔨.U ≤ normalizer ((⁅𝔨.U, zpowers y⁆ : Subgroup G) : Set G) := fun g hg =>
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => hUab w (hWU hw) g hg)
    have hN := 𝔨.inf_normalizer_eq_Pstar_of h48i hXN₀ _ hWV hW1 hAW hUW
    intro g hg
    obtain ⟨⟨hgR, hgN⟩, hgy⟩ := hg
    have hgW : g ∈ normalizer ((⁅𝔨.U, zpowers y⁆ : Subgroup G) : Set G) :=
      mem_normalizer_commutator_zpowers hgN (mem_centralizer_singleton_iff.mp hgy)
    have hgP : g ∈ 𝔨.P ⊓ normalizer ((⁅𝔨.U, zpowers y⁆ : Subgroup G) : Set G) := ⟨hgR.1, hgW⟩
    rw [hN] at hgP
    rw [← 𝔨.R_inf_Pstar]
    exact ⟨hgR, hgP⟩
  ·
    have hAU' : A ≤ normalizer ((⁅𝔨.U, 𝔨.U⁆ : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_commutator (𝔨.A_le_normalizer_U ha) (𝔨.A_le_normalizer_U ha)
    have hUU' : 𝔨.U ≤ normalizer ((⁅𝔨.U, 𝔨.U⁆ : Subgroup G) : Set G) := fun g hg =>
      mem_normalizer_commutator (le_normalizer hg) (le_normalizer hg)
    have hN := 𝔨.inf_normalizer_eq_Pstar_of h48i hXN₀ _ 𝔨.commutator_U_le_V hU' hAU' hUU'
    intro g hg
    obtain ⟨hgR, hgN⟩ := hg
    have hgP : g ∈ 𝔨.P ⊓ normalizer ((⁅𝔨.U, 𝔨.U⁆ : Subgroup G) : Set G) :=
      ⟨hgR.1, mem_normalizer_commutator hgN hgN⟩
    rw [hN] at hgP
    rw [← 𝔨.R_inf_Pstar]
    exact ⟨hgR, hgP⟩

theorem V_le_R : 𝔨.V ≤ 𝔨.R := 𝔨.V_le_U.trans 𝔨.U_le_R

theorem A_le_normalizer_V : A ≤ normalizer (𝔨.V : Set G) := fun _ ha =>
  𝔨.K₁_le_normalizer_V (𝔨.A_le_K₁ ha)

theorem commutator_Pstar_X_eq_bot_of_isKleinFour
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (h4 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsKleinFour L)) :
    ⁅𝔨.Pstar, ρ.X⁆ = ⊥ := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  obtain ⟨W, hWKN, hXW, hWn, -, hcov, hker, -⟩ := 𝔨.exists_W_K₁
  obtain ⟨L, _, ⟨e⟩, hL⟩ := quotIs_bar_inf ρ.O_N_le_N₀ ρ.N₀_le_normalizer_O_N
    (hWKN.trans inf_le_left) (hWKN.trans inf_le_right) hcov hker h4
  have hcardW : Nat.card (bar 𝔨.K₁ W) = 4 := by
    have := hL
    rw [Nat.card_congr e.toEquiv]
    exact IsKleinFour.card_four
  have hEK₁ : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.K₁ := 𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_K₁
  have hEJ : bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆ ≤ bar 𝔨.K₁ W := by
    rw [bar_commutator 𝔨.Pstar_le_K₁ 𝔨.X_le_K₁]
    exact (commutator_mono le_rfl (bar_mono hXW)).trans (commutator_le_right _ _)
  have hp' : IsPGroup p (bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆) :=
    IsPGroup.bar (𝔨.isPGroup_of_le_P (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)) hEK₁
  have hbot : bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆ = ⊥ := by
    obtain ⟨n, hn⟩ := hp'.exists_card_eq
    have hdvd : Nat.card (bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆) ∣ 2 ^ 2 := by
      have := card_dvd_of_le hEJ
      rwa [hcardW] at this
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      have hpd : p ∣ 2 ^ 2 := (dvd_pow_self p hn0).trans hdvd
      exact 𝔨.hp2 ((Nat.prime_dvd_prime_iff_eq 𝔨.hp Nat.prime_two).mp
        (𝔨.hp.dvd_of_dvd_pow hpd))
    rw [hn0, pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  have hEO : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.V := by
    rw [← 𝔨.Pstar_inf_O_K₁]
    refine le_inf 𝔨.commutator_Pstar_X_le_Pstar fun e he => ?_
    have h1 : (QuotientGroup.mk ⟨e, hEK₁ he⟩ : Bar 𝔨.K₁) ∈ bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆ :=
      mem_bar_iff.mpr ⟨_, he, rfl⟩
    rw [hbot, mem_bot, mk_eq_one_iff_mem_O] at h1
    exact h1
  rw [← (𝔨.isCyclic_commutator_Pstar_X_of hP2b5 hP2b6).2]
  refine le_antisymm (le_inf le_rfl fun e he => ?_) inf_le_left
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_iff.mp (𝔨.X_le_centralizer_V hx) e (hEO he)).symm

theorem le_C_of_Pstar_le_C (Q : Subgroup G) (hQP : Q ≤ 𝔨.P) (hAQ : A ≤ normalizer (Q : Set G))
    (hPQ : 𝔨.P ≤ normalizer (Q : Set G)) {x : G} (hx : x ∈ ρ.X) (hPx : 𝔨.Pstar ≤ C x) :
    Q ≤ C x := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  by_cases hx1 : x = 1
  · intro q _
    rw [hx1]
    exact mem_centralizer_singleton_iff.mpr (by group)
  have hxo : orderOf x = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_X hx hx1
  have hxQ : x ∈ normalizer (Q : Set G) := hAQ (ρ.X_le_A hx)
  have hVP : 𝔨.V ≤ 𝔨.P := 𝔨.V_le_Pstar.trans 𝔨.Pstar_le_P
  have hle := CFSG.RankThree.PartTwo.Sec18.Item188Proof.centralizes_of_thompson_AxB
    (𝔨.isPGroup_of_le_P hQP)
    (by
      rw [Nat.card_zpowers, hxo]
      exact Nat.coprime_two_left.mpr 𝔨.odd_p)
    (𝔨.isPGroup_of_le_P hVP) (zpowers_le.mpr hxQ) (hVP.trans hPQ)
    (by
      rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
      intro v hv
      exact mem_centralizer_iff.mp (𝔨.X_le_centralizer_V hx) v hv)
    (fun q hq => by
      have hqx : q * x = x * q := mem_centralizer_singleton_iff.mp
        (hPx (𝔨.P_inf_centralizer_V_le_Pstar ⟨hQP hq.1, hq.2⟩))
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute x q from hqx.symm) n).eq)
  intro q hq
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp (hle hq) x (mem_zpowers x)).symm

theorem lemma_5_9_of (Q : Subgroup G) (hQP : Q ≤ 𝔨.P) (hAQ : A ≤ normalizer (Q : Set G))
    (hPQ : 𝔨.P ≤ normalizer (Q : Set G)) (hQY : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ Q ≤ C y)
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀)
    (h45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A H P₁ →
      IsMaxInvIn p A H P₂ → ∃ g ∈ H ⊓ normalizer (A : Set G),
        P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h56 : ∀ K : Subgroup G, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
      ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H))) :
    ∃ W : Subgroup G, Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
      W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅ρ.X, W⁆ = W := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  obtain ⟨x₁, hx₁X, hx₁1, hPx₁⟩ := 𝔨.exists_Pstar_le_C_of hP2b6
  obtain ⟨x₂, hx₂X, hx₂o, -, -, hXeq⟩ :=
    exists_zpowers_sup_zpowers_eq_of_mem ρ.isKleinFour_X hx₁X hx₁1
  have hQx₁ := 𝔨.le_C_of_Pstar_le_C Q hQP hAQ hPQ hx₁X hPx₁
  obtain ⟨hEcyc, hEC⟩ := 𝔨.isCyclic_commutator_Pstar_X_of hP2b5 hP2b6
  have hEP : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.Pstar := 𝔨.commutator_Pstar_X_le_Pstar
  have hx₂x₂ : x₂ * x₂ = 1 := by rw [← sq, ← hx₂o, pow_orderOf_eq_one]
  have hAC : A ≤ centralizer (ρ.X : Set G) := fun a ha => mem_centralizer_iff.mpr fun x hx =>
    ρ.comm (ρ.X_le_A hx) ha
  have hEab : ∀ a ∈ ⁅𝔨.Pstar, ρ.X⁆, ∀ b ∈ ⁅𝔨.Pstar, ρ.X⁆, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      ((IsCyclic.commutative (α := ↥(⁅𝔨.Pstar, ρ.X⁆ : Subgroup G))).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinvE : ∀ e ∈ ⁅𝔨.Pstar, ρ.X⁆, x₂ * e * x₂⁻¹ = e⁻¹ := by
    intro e he
    have he' : x₂ * e * x₂⁻¹ ∈ ⁅𝔨.Pstar, ρ.X⁆ :=
      (mem_normalizer_iff.mp (𝔨.X_le_normalizer_commutator_Pstar_X hx₂X) e).mp he
    have hc : x₂ * (e * (x₂ * e * x₂⁻¹)) * x₂⁻¹ = e * (x₂ * e * x₂⁻¹) := by
      calc x₂ * (e * (x₂ * e * x₂⁻¹)) * x₂⁻¹ =
            (x₂ * e * x₂⁻¹) * ((x₂ * x₂) * e * (x₂⁻¹ * x₂⁻¹)) := by group
        _ = (x₂ * e * x₂⁻¹) * e := by rw [hx₂x₂, ← mul_inv_rev, hx₂x₂, inv_one, one_mul, mul_one]
        _ = e * (x₂ * e * x₂⁻¹) := hEab _ he' _ he
    have hf : e * (x₂ * e * x₂⁻¹) ∈ ⁅𝔨.Pstar, ρ.X⁆ ⊓ centralizer (ρ.X : Set G) :=
      ⟨mul_mem he he', mem_centralizer_of_commute_of_eq_sup hXeq (hPx₁ (hEP (mul_mem he he')))
        (mem_centralizer_singleton_iff.mpr (commute_of_conj_eq hc))⟩
    rw [hEC, mem_bot] at hf
    exact eq_inv_of_mul_eq_one_right hf
  have : IsCyclic (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) := hEcyc
  set W := ⁅𝔨.Pstar, ρ.X⁆ ⊓ Q with hW
  have hWE : W ≤ ⁅𝔨.Pstar, ρ.X⁆ := inf_le_left
  have hWQ : W ≤ Q := inf_le_right
  have hAW : A ≤ normalizer (W : Set G) := fun a ha => inf_normalizer_le_normalizer_inf
    ⟨mem_normalizer_commutator (𝔨.A_le_normalizer_Pstar ha)
      (centralizer_le_normalizer _ (hAC ha)), hAQ ha⟩
  have hQx₂ : Q ⊓ C x₂ ≤ 𝔨.R := fun q hq =>
    ⟨hQP hq.1, mem_centralizer_of_commute_of_eq_sup hXeq (hQx₁ hq.1) hq.2⟩
  have hmain : Q ≤ (𝔨.R ⊓ Q) ⊔ W := by
    by_contra hQM
    obtain ⟨L, i, f, hf, hk, hL⟩ := h48i
    rcases hL with hL | hL
    swap
    ·
      have hEb := 𝔨.commutator_Pstar_X_eq_bot_of_isKleinFour hP2b5 hP2b6 ⟨L, i, f, hf, hk, hL⟩
      apply hQM
      intro q hq
      refine mem_sup_left ⟨⟨hQP hq, mem_centralizer_iff.mpr fun x hx => ?_⟩, hq⟩
      have hPx : 𝔨.Pstar ≤ C x := fun y hy => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hEb hy) x hx).symm
      exact (mem_centralizer_singleton_iff.mp (𝔨.le_C_of_Pstar_le_C Q hQP hAQ hPQ hx hPx hq)).symm
    have hns : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5) := ⟨L, i, f, hf, hk, hL⟩
    have h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) :=
      ⟨L, i, f, hf, hk, Or.inl hL⟩
    have hRU := 𝔨.lemma_5_8_of Q hQP hAQ hPQ hQY h48i hXN₀
    have hRX : 𝔨.R ≤ centralizer (ρ.X : Set G) := inf_le_right
    have hRP : 𝔨.R ≤ 𝔨.Pstar := hRU.le.trans 𝔨.U_le_Pstar
    have hRW : 𝔨.R ⊓ W = ⊥ := by
      rw [eq_bot_iff, ← hEC]
      exact fun x hx => ⟨hWE hx.2, hRX hx.1⟩
    have hRNW : 𝔨.R ≤ normalizer (W : Set G) := fun r hr => inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_commutator (le_normalizer (hRP hr))
        (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (hRX hr) x hx)), hPQ hr.1⟩
    have hRNQ : 𝔨.R ≤ normalizer (Q : Set G) := inf_le_left.trans hPQ
    set M := 𝔨.R ⊔ W with hM
    have hAR : A ≤ normalizer (𝔨.R : Set G) := fun a ha => inf_normalizer_le_normalizer_inf
      ⟨𝔨.A_le_normalizer_P ha, le_normalizer (hAC ha)⟩
    have hAM : A ≤ normalizer (M : Set G) := fun a ha =>
      mem_normalizer_sup_of_mem (hAR ha) (hAW ha)
    have hNM : ¬ Q ⊓ normalizer (M : Set G) ≤ M := by
      intro hNQ
      have hMRQ : M ≤ 𝔨.R ⊔ Q := sup_le_sup_left hWQ _
      have hRQ : ((𝔨.R ⊔ Q : Subgroup G) : Set G) = (𝔨.R : Set G) * (Q : Set G) :=
        coe_mul_of_left_le_normalizer_right _ _ hRNQ
      have heq : 𝔨.R ⊔ Q = M := by
        refine eq_of_inf_normalizer_le (𝔨.isPGroup_of_le_P (sup_le inf_le_left hQP)) hMRQ ?_
        rintro h ⟨hhRQ, hhN⟩
        have hh : h ∈ ((𝔨.R ⊔ Q : Subgroup G) : Set G) := hhRQ
        rw [hRQ] at hh
        obtain ⟨r, hr, q, hq, rfl⟩ := Set.mem_mul.mp hh
        have hrM : r ∈ M := mem_sup_left hr
        have hqN : q ∈ normalizer (M : Set G) := by
          have := mul_mem (inv_mem (le_normalizer hrM)) hhN
          rwa [inv_mul_cancel_left] at this
        exact mul_mem hrM (hNQ ⟨hq, hqN⟩)
      apply hQM
      intro q hq
      have hqM : q ∈ ((M : Subgroup G) : Set G) := by
        rw [← heq]
        exact mem_sup_right hq
      rw [hM, coe_mul_of_left_le_normalizer_right _ _ hRNW] at hqM
      obtain ⟨r, hr, w, hw, rfl⟩ := Set.mem_mul.mp hqM
      have hrQ : r ∈ Q := by
        have := mul_mem hq (inv_mem (hWQ hw))
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (mem_sup_left ⟨hr, hrQ⟩) (mem_sup_right hw)
    have hAN : A ≤ normalizer ((Q ⊓ normalizer (M : Set G) : Subgroup G) : Set G) :=
      fun a ha => inf_normalizer_le_normalizer_inf ⟨hAQ ha, le_normalizer (hAM ha)⟩
    have hNodd : Odd (Nat.card (Q ⊓ normalizer (M : Set G) : Subgroup G)) :=
      𝔨.odd_card_of_le_P (inf_le_left.trans hQP)
    obtain ⟨g, hgN, hgM, hgx₂, hgA⟩ := exists_mem_not_mem_conj_eq_inv ρ.hA.1 hNodd hAN hNM
      (ρ.X_le_A hx₂X) fun q hq => mem_sup_left (hQx₂ ⟨hq.1.1, hq.2⟩)
    have hgQ : g ∈ Q := hgN.1
    have hgNM : g ∈ normalizer (M : Set G) := hgN.2
    have hVR : 𝔨.V ≤ 𝔨.R := 𝔨.V_le_R
    obtain ⟨E₂, hE₂V, hE₂ab, hE₂card⟩ := exists_isElemAbelian_card_eq_sq 𝔨.hp 𝔨.hp2
      (𝔨.isPGroup_of_le_P (𝔨.V_le_Pstar.trans 𝔨.Pstar_le_P)) ρ.isKleinFour_Y
      (ρ.Y_le_A.trans 𝔨.A_le_normalizer_V) (𝔨.lemma_5_7_of Q hQP hAQ hPQ hQY)
    set F := E₂.map (MulAut.conj g).toMonoidHom with hF
    have hFcard : Nat.card F = p ^ 2 := by
      rw [hF, card_map_of_injective (MulAut.conj g).injective, hE₂card]
    have hFM : F ≤ M := by
      rintro _ ⟨e, he, rfl⟩
      exact (mem_normalizer_iff.mp hgNM e).mp (mem_sup_left (hVR (hE₂V he)))
    have hFp : ∀ x ∈ F, x ^ p = 1 := by
      rintro _ ⟨e, he, rfl⟩
      change (g * e * g⁻¹) ^ p = 1
      rw [conj_pow, hE₂ab.2 e he, mul_one, mul_inv_cancel]
    have : IsCyclic W := Subgroup.isCyclic_of_le hWE
    have hWp : IsPGroup p W := 𝔨.isPGroup_of_le_P (hWE.trans (hEP.trans 𝔨.Pstar_le_P))
    obtain ⟨W₁, hW₁W, hW₁card, hW₁mem, hW₁N⟩ :=
      exists_le_card_le_of_isCyclic (p := p) 𝔨.hp.pos (W := W)
    have hFW₁ : F ≤ W₁ ⊔ 𝔨.R := by
      intro x hx
      have hxM : x ∈ ((M : Subgroup G) : Set G) := hFM hx
      rw [hM, coe_mul_of_left_le_normalizer_right _ _ hRNW] at hxM
      obtain ⟨r, hr, w, hw, rfl⟩ := Set.mem_mul.mp hxM
      have hwp := pow_eq_one_of_mul_pow_eq_one 𝔨.hp 𝔨.hp2 hWp hRNW hRW hr hw (hFp _ hx)
      exact mul_mem (mem_sup_right hr) (mem_sup_left (hW₁mem w hw hwp))
    have hW₁R : W₁ ⊓ 𝔨.R = ⊥ := by
      rw [eq_bot_iff, ← hRW]
      exact fun x hx => ⟨hx.2, hW₁W hx.1⟩
    have hcardJ := card_le_mul_card_inf_of_le_sup (hRNW.trans hW₁N) hW₁R hW₁card hFW₁
    have hgodd : Odd (orderOf g) :=
      (𝔨.odd_card_of_le_P hQP).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hgQ)
    have hJ : 𝔨.R ⊓ F ≤ 𝔨.V ⊓ C g := by
      rintro _ ⟨hjR, ⟨e, he, rfl⟩⟩
      change g * e * g⁻¹ ∈ 𝔨.V ⊓ C g
      have hfix : ∀ y ∈ 𝔨.R, x₂ * y * x₂⁻¹ = y := fun y hy => by
        rw [mem_centralizer_iff.mp (hRX hy) x₂ hx₂X, mul_inv_cancel_right]
      have hge := mul_comm_of_conj_eq_inv_of_conj_eq hgodd hgx₂ (hfix e (hVR (hE₂V he)))
        (hfix _ hjR)
      rw [show g * e * g⁻¹ = e by rw [hge, mul_inv_cancel_right]]
      exact ⟨hE₂V he, mem_centralizer_singleton_iff.mpr hge.symm⟩
    set Vs := 𝔨.V ⊓ C g with hVs
    have hVs1 : Vs ≠ ⊥ := by
      intro h
      rw [h, le_bot_iff] at hJ
      rw [hJ, card_bot, mul_one, hFcard] at hcardJ
      have hp1 := 𝔨.hp.one_lt
      nlinarith
    have hAVs : A ≤ normalizer (Vs : Set G) := by
      intro a ha
      refine inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_V ha, ?_⟩
      refine mem_normalizer_fintype fun v hv => ?_
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hv ⊢
      have hc : (a * v * a⁻¹) * (a * g * a⁻¹) = (a * g * a⁻¹) * (a * v * a⁻¹) := by
        calc (a * v * a⁻¹) * (a * g * a⁻¹) = a * (v * g) * a⁻¹ := by group
          _ = a * (g * v) * a⁻¹ := by rw [hv]
          _ = (a * g * a⁻¹) * (a * v * a⁻¹) := by group
      rcases hgA a ha with h | h
      · rwa [h] at hc
      · rw [h] at hc
        calc a * v * a⁻¹ * g = g * (g⁻¹ * (a * v * a⁻¹)) * g := by group
          _ = g * ((a * v * a⁻¹) * g⁻¹) * g := by rw [hc]
          _ = g * (a * v * a⁻¹) := by group
    have hC5 := 𝔨.commutator_inf_normalizer_le_Pstar_of hXN₀ h45 h56 h1N hP2b5 hP2b6 Vs
      inf_le_left hVs1 hAVs hns
    have hgVs : g ∈ 𝔨.P ⊓ normalizer (Vs : Set G) := by
      refine ⟨hQP hgQ, mem_normalizer_fintype fun v hv => ?_⟩
      have hvg : v * g = g * v := mem_centralizer_singleton_iff.mp hv.2
      rw [← hvg, mul_inv_cancel_right]
      exact hv
    have hgP : g ∈ 𝔨.Pstar := hC5 (commutator_mono le_rfl (zpowers_le.mpr hx₂X)
      (mem_commutator_zpowers_of_conj_eq_inv (𝔨.odd_card_of_le_P inf_le_left) hgVs hgx₂))
    have hgE : g ∈ ⁅𝔨.Pstar, ρ.X⁆ := commutator_mono le_rfl (zpowers_le.mpr hx₂X)
      (mem_commutator_zpowers_of_conj_eq_inv (𝔨.odd_card_of_le_P 𝔨.Pstar_le_P) hgP hgx₂)
    exact hgM (mem_sup_right ⟨hgE, hgQ⟩)
  refine ⟨W, le_antisymm hmain (sup_le inf_le_right hWQ), Subgroup.isCyclic_of_le hWE, hAW,
    le_inf (hWE.trans (hEP.trans 𝔨.Pstar_le_K₁)) (hWE.trans 𝔨.commutator_Pstar_X_le_centralizer_V),
    ?_⟩
  rw [commutator_comm]
  refine le_antisymm (commutator_le_left_of_le_normalizer fun x hx => hAW (ρ.X_le_A hx)) ?_
  intro w hw
  exact commutator_mono le_rfl (zpowers_le.mpr hx₂X)
    (mem_commutator_zpowers_of_conj_eq_inv (𝔨.odd_card_of_le_P (hWQ.trans hQP)) hw
      (hinvE w (hWE hw)))

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem lemma_5_7_of
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a) :
    ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔠.V ≤ C y :=
  𝔠.toSec5KConfig.lemma_5_7_of 𝔠.Q 𝔠.Q_le_P 𝔠.A_le_normalizer_Q 𝔠.P_le_normalizer_Q
    (𝔠.not_Q_le_C_of hP2b12)

theorem lemma_5_8_of
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a)
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀) :
    𝔠.R = 𝔠.U :=
  𝔠.toSec5KConfig.lemma_5_8_of 𝔠.Q 𝔠.Q_le_P 𝔠.A_le_normalizer_Q 𝔠.P_le_normalizer_Q
    (𝔠.not_Q_le_C_of hP2b12) h48i hXN₀

theorem R_inf_Q_eq : 𝔠.R ⊓ 𝔠.Q = 𝔠.Q ⊓ centralizer (ρ.X : Set G) := by
  change 𝔠.P ⊓ centralizer (ρ.X : Set G) ⊓ 𝔠.Q = 𝔠.Q ⊓ centralizer (ρ.X : Set G)
  rw [inf_comm, ← inf_assoc, inf_of_le_left 𝔠.Q_le_P]

theorem not_R_inf_Q_le_centralizer_Y_of
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a) :
    ¬ 𝔠.R ⊓ 𝔠.Q ≤ centralizer (ρ.Y : Set G) := by
  intro hRQ
  have hV₀ : 𝔠.V ⊓ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ≤ centralizer (ρ.Y : Set G) := by
    refine le_trans ?_ hRQ
    rw [← 𝔠.R_inf_O_H₁]
    exact inf_le_inf_right _ 𝔠.V_le_R
  obtain ⟨W, -, hYW, hWn, hWt⟩ := 𝔠.exists_W_H₁
  have hYJ : bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ρ.Y ≤
      bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W := bar_mono hYW
  have hYV : ρ.Y ≤ normalizer (𝔠.V : Set G) := ρ.Y_le_A.trans 𝔠.A_le_normalizer_V
  have hVP : 𝔠.V ≤ 𝔠.P := 𝔠.V_le_Pstar.trans 𝔠.Pstar_le_P
  have hVH₁ : 𝔠.V ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := hVP.trans 𝔠.P_le_H₁
  have hVY : ⁅𝔠.V, ρ.Y⁆ ≤ 𝔠.V := commutator_le_left_of_le_normalizer hYV
  have hKL : bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ⁅𝔠.V, ρ.Y⁆ ≤
      bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W := by
    rw [bar_commutator hVH₁ 𝔠.Y_le_H₁]
    exact (commutator_mono le_rfl hYJ).trans (commutator_le_right _ _)
  have hKodd : Odd (Nat.card (bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ⁅𝔠.V, ρ.Y⁆)) :=
    (𝔠.odd_card_of_le_P (hVY.trans hVP)).of_dvd_nat (card_bar_dvd (hVY.trans hVH₁))
  have hKN := bar_le_normalizer (H := 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))
    (K := ⁅𝔠.V, ρ.Y⁆) (L := ρ.Y)
    fun _ hy => mem_normalizer_commutator (hYV hy) (le_normalizer hy)
  obtain ⟨a, ha, ha1, hle⟩ := hP2b6 (Or.inl hWt)
    (isKleinFour_bar ρ.isKleinFour_Y 𝔠.Y_le_H₁ (ρ.Y_inf_O_eq_bot _)) hYJ hKL hKodd hKN
  obtain ⟨y, hy, rfl⟩ := mem_bar_iff.mp ha
  have hy1 : (y : G) ≠ 1 := fun h =>
    ha1 (by rw [show y = 1 from Subtype.ext h, QuotientGroup.mk_one])
  have hyo : orderOf (y : G) = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_Y hy hy1
  have hyV : (y : G) ∈ normalizer (𝔠.V : Set G) := hYV hy
  have hE : ⁅⁅𝔠.V, zpowers (y : G)⁆, zpowers (y : G)⁆ ≤
      𝔠.V ⊓ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) := by
    rw [commutator_le]
    intro e he s hs
    rcases eq_one_or_eq_of_mem_zpowers hyo hs with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    · have heV : e ∈ 𝔠.V := commutator_zpowers_le_of_mem_normalizer hyV he
      refine ⟨commutator_zpowers_le_of_mem_normalizer hyV
        (commutator_mem_commutator heV (mem_zpowers _)), ?_⟩
      have heK : e ∈ ⁅𝔠.V, ρ.Y⁆ := commutator_mono le_rfl (zpowers_le.mpr hy) he
      have heH : e ∈ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := hVH₁ heV
      have hc := hle (mem_bar_iff.mpr ⟨⟨e, heH⟩, heK, rfl⟩)
      rw [mem_centralizer_singleton_iff] at hc
      have h1 : (QuotientGroup.mk (⟨e, heH⟩ * y * ⟨e, heH⟩⁻¹ * y⁻¹) :
          Bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, hc]
        group
      rw [mk_eq_one_iff_mem_O] at h1
      simpa [commutatorElement_def] using h1
  have hVodd := 𝔠.odd_card_of_le_P hVP
  have hEodd : Odd (Nat.card (⁅𝔠.V, zpowers (y : G)⁆ : Subgroup G)) :=
    𝔠.odd_card_of_le_P ((commutator_zpowers_le_of_mem_normalizer hyV).trans hVP)
  have h1 := commutator_zpowers_eq_bot_of_le hEodd hyo
    (mem_normalizer_commutator_zpowers hyV rfl) hE fun v hv =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hV₀ hv) _ hy).symm
  rw [commutator_commutator_zpowers_eq hVodd hyo hyV] at h1
  refine 𝔠.lemma_5_7_of hP2b12 y hy hy1 fun v hv => ?_
  have h2 := commutator_mem_commutator hv (mem_zpowers (y : G))
  rw [h1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact mem_centralizer_singleton_iff.mpr h2

theorem exists_isElemAbelian_le_R_inf_Q_of
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a) :
    ∃ E : Subgroup G, E ≤ 𝔠.R ⊓ 𝔠.Q ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  obtain ⟨u, ⟨⟨-, huQ⟩, huX⟩, huY, -, hufix⟩ := 𝔠.exists_three_element_of hP2b12
  have huRQ : u ∈ normalizer ((𝔠.R ⊓ 𝔠.Q : Subgroup G) : Set G) := by
    rw [𝔠.R_inf_Q_eq]
    exact inf_normalizer_le_normalizer_inf ⟨huQ, le_normalizer huX⟩
  have hYRQ : ρ.Y ≤ normalizer ((𝔠.R ⊓ 𝔠.Q : Subgroup G) : Set G) := fun y hy =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.Y_le_normalizer_R hy, (𝔠.A_le_H₁ (ρ.Y_le_A hy)).2⟩
  exact exists_isElemAbelian_card_eq_pow_three 𝔠.hp 𝔠.hp2
    (𝔠.isPGroup_of_le_P (inf_le_left.trans inf_le_left)) ρ.isKleinFour_Y hYRQ huY huRQ hufix
    (𝔠.not_R_inf_Q_le_centralizer_Y_of hP2b6 hP2b12)

theorem lemma_5_9_of
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a)
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀)
    (h45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A H P₁ →
      IsMaxInvIn p A H P₂ → ∃ g ∈ H ⊓ normalizer (A : Set G),
        P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h56 : ∀ K : Subgroup G, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
      ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H))) :
    ∃ W : Subgroup G, 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
      W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W :=
  𝔠.toSec5KConfig.lemma_5_9_of 𝔠.Q 𝔠.Q_le_P 𝔠.A_le_normalizer_Q 𝔠.P_le_normalizer_Q
    (𝔠.not_Q_le_C_of hP2b12) hP2b5 hP2b6 h48i hXN₀ h45 h56 h1N

end Sec5ConfigR

end CFSG.GH72
