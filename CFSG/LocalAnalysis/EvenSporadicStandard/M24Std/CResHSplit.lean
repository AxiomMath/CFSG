module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Nat.Prime.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH

open Subgroup

variable {V : Type*} [CommGroup V]

@[expose] def plusPart (s : MulAut V) (U : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ s u = u}
  mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨U.one_mem, map_one s⟩
  inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by rw [map_inv, ha.2]⟩

@[expose] def minusPart (s : MulAut V) (U : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ s u = u⁻¹}
  mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2, mul_inv]⟩
  one_mem' := ⟨U.one_mem, by rw [map_one, inv_one]⟩
  inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by rw [map_inv, ha.2]⟩

@[expose] def fixPart (S : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ t ∈ S, t u = u}
  mul_mem' := fun {a b} ha hb =>
    ⟨U.mul_mem ha.1 hb.1, fun t ht => by rw [map_mul, ha.2 t ht, hb.2 t ht]⟩
  one_mem' := ⟨U.one_mem, fun t _ => map_one t⟩
  inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, fun t ht => by rw [map_inv, ha.2 t ht]⟩

@[expose] def IsInvariant (S : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∀ s ∈ S, ∀ u ∈ U, s u ∈ U

@[simp] theorem mem_plusPart {s : MulAut V} {U : Subgroup V} {u : V} :
    u ∈ plusPart s U ↔ u ∈ U ∧ s u = u := Iff.rfl

@[simp] theorem mem_minusPart {s : MulAut V} {U : Subgroup V} {u : V} :
    u ∈ minusPart s U ↔ u ∈ U ∧ s u = u⁻¹ := Iff.rfl

@[simp] theorem mem_fixPart {S : Subgroup (MulAut V)} {U : Subgroup V} {u : V} :
    u ∈ fixPart S U ↔ u ∈ U ∧ ∀ t ∈ S, t u = u := Iff.rfl

theorem fixPart_le (S : Subgroup (MulAut V)) (U : Subgroup V) : fixPart S U ≤ U :=
  fun _ hu => hu.1

theorem plusPart_minusPart (s t : MulAut V) (U : Subgroup V) :
    plusPart s (minusPart t U) = minusPart t (plusPart s U) := by
  ext u; simp only [mem_plusPart, mem_minusPart]; tauto

theorem minusPart_minusPart (s t : MulAut V) (U : Subgroup V) :
    minusPart s (minusPart t U) = minusPart t (minusPart s U) := by
  ext u; simp only [mem_minusPart]; tauto

theorem plusPart_fixPart (s : MulAut V) (S : Subgroup (MulAut V)) (U : Subgroup V) :
    plusPart s (fixPart S U) = fixPart S (plusPart s U) := by
  ext u; simp only [mem_plusPart, mem_fixPart]; tauto

theorem minusPart_fixPart (s : MulAut V) (S : Subgroup (MulAut V)) (U : Subgroup V) :
    minusPart s (fixPart S U) = fixPart S (minusPart s U) := by
  ext u; simp only [mem_minusPart, mem_fixPart]; tauto

structure Setup (p : ℕ) {V : Type*} [CommGroup V] (S : Subgroup (MulAut V)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  pow_eq_one : ∀ v : V, v ^ p = 1
  mul_self : ∀ s ∈ S, s * s = 1
  comm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s

namespace Setup

variable {p : ℕ} {S : Subgroup (MulAut V)} (h : Setup p S)
include h

theorem apply_apply {s : MulAut V} (hs : s ∈ S) (v : V) : s (s v) = v := by
  rw [← MulAut.mul_apply, h.mul_self s hs, MulAut.one_apply]

theorem comm_apply {s t : MulAut V} (hs : s ∈ S) (ht : t ∈ S) (v : V) : s (t v) = t (s v) := by
  rw [← MulAut.mul_apply, h.comm s hs t ht, MulAut.mul_apply]

theorem eq_one_of_eq_inv {u : V} (hu : u = u⁻¹) : u = 1 := by
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 hu
  obtain ⟨k, hk⟩ := h.prime.odd_of_ne_two h.ne_two
  calc u = u ^ p := by rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
    _ = 1 := h.pow_eq_one u

theorem disjoint_parts (s : MulAut V) (U : Subgroup V) :
    Disjoint (plusPart s U) (minusPart s U) := by
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  exact h.eq_one_of_eq_inv (hx.2.symm.trans hx'.2)

theorem exists_mul_eq {s : MulAut V} (hs : s ∈ S) {U : Subgroup V} (hU : ∀ u ∈ U, s u ∈ U)
    {u : V} (hu : u ∈ U) : ∃ a ∈ plusPart s U, ∃ b ∈ minusPart s U, a * b = u := by
  obtain ⟨k, hk⟩ := h.prime.odd_of_ne_two h.ne_two
  have hsu := hU u hu
  refine ⟨(u * s u) ^ (k + 1), ⟨?_, ?_⟩, (u * (s u)⁻¹) ^ (k + 1), ⟨?_, ?_⟩, ?_⟩
  · exact U.pow_mem (U.mul_mem hu hsu) _
  · rw [map_pow, map_mul, h.apply_apply hs, mul_comm]
  · exact U.pow_mem (U.mul_mem hu (U.inv_mem hsu)) _
  · rw [map_pow, map_mul, map_inv, h.apply_apply hs, ← inv_pow, mul_inv_rev, inv_inv]
  · rw [← mul_pow, mul_mul_mul_comm, mul_inv_cancel, mul_one, ← pow_two, ← pow_mul]
    have : 2 * (k + 1) = p + 1 := by omega
    rw [this, pow_succ, h.pow_eq_one, one_mul]

theorem card_eq_mul [Finite V] {s : MulAut V} (hs : s ∈ S) {U : Subgroup V}
    (hU : ∀ u ∈ U, s u ∈ U) :
    Nat.card U = Nat.card (plusPart s U) * Nat.card (minusPart s U) := by
  let f : plusPart s U × minusPart s U → U := fun x => ⟨x.1 * x.2, U.mul_mem x.1.2.1 x.2.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
      have hab' : a * b = a' * b' := congrArg Subtype.val hab
      have h1 : a / a' = b' / b := by
        rw [div_eq_div_iff_mul_eq_mul, mul_comm b' a', hab']
      have h2 : a / a' = 1 :=
        (Subgroup.disjoint_def.1 (h.disjoint_parts s U)) (div_mem ha ha')
          (h1 ▸ div_mem hb' hb)
      have h3 : a = a' := div_eq_one.1 h2
      have h4 : b = b' := by
        rw [h3] at hab'
        exact mul_left_cancel hab'
      subst h3 h4
      rfl
    · rintro ⟨u, hu⟩
      obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_eq hs hU hu
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem isInvariant_plusPart {s : MulAut V} (hs : s ∈ S) {U : Subgroup V}
    (hU : IsInvariant S U) : IsInvariant S (plusPart s U) := fun t ht u hu =>
  ⟨hU t ht u hu.1, by rw [h.comm_apply hs ht, hu.2]⟩

theorem isInvariant_minusPart {s : MulAut V} (hs : s ∈ S) {U : Subgroup V}
    (hU : IsInvariant S U) : IsInvariant S (minusPart s U) := fun t ht u hu =>
  ⟨hU t ht u hu.1, by rw [h.comm_apply hs ht, hu.2, map_inv]⟩

theorem isInvariant_fixPart {U : Subgroup V} (hU : IsInvariant S U) :
    IsInvariant S (fixPart S U) := fun t ht u hu =>
  ⟨hU t ht u hu.1, fun s hs => by rw [h.comm_apply hs ht, hu.2 s hs]⟩

theorem induction [Finite V] {P : Subgroup V → Prop}
    (base : ∀ U, IsInvariant S U → (∀ t ∈ S, (∀ u ∈ U, t u = u) ∨ ∀ u ∈ U, t u = u⁻¹) → P U)
    (step : ∀ U, IsInvariant S U → ∀ s ∈ S, (∃ u ∈ U, s u ≠ u) → (∃ u ∈ U, s u ≠ u⁻¹) →
      P (plusPart s U) → P (minusPart s U) → P U) :
    ∀ U, IsInvariant S U → P U := by
  suffices H : ∀ n, ∀ U : Subgroup V, Nat.card U = n → IsInvariant S U → P U from
    fun U => H _ U rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hn hU
    by_cases hpm : ∀ t ∈ S, (∀ u ∈ U, t u = u) ∨ ∀ u ∈ U, t u = u⁻¹
    · exact base U hU hpm
    · push Not at hpm
      obtain ⟨s, hs, ⟨u₁, hu₁, h₁⟩, ⟨u₂, hu₂, h₂⟩⟩ := hpm
      have hsU : ∀ u ∈ U, s u ∈ U := hU s hs
      have hcard := h.card_eq_mul hs hsU
      have hA : 1 < Nat.card (plusPart s U) := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_eq hs hsU hu₂
        have ha1 : a = 1 := by rw [hbot] at ha; exact (Subgroup.mem_bot.1 ha)
        rw [ha1, one_mul] at hab
        exact h₂ (hab ▸ hb.2)
      have hB : 1 < Nat.card (minusPart s U) := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul_eq hs hsU hu₁
        have hb1 : b = 1 := by rw [hbot] at hb; exact (Subgroup.mem_bot.1 hb)
        rw [hb1, mul_one] at hab
        exact h₁ (hab ▸ ha.2)
      refine step U hU s hs ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩ ?_ ?_
      · refine ih (Nat.card (plusPart s U)) ?_ _ rfl (h.isInvariant_plusPart hs hU)
        rw [← hn, hcard]
        exact lt_mul_of_one_lt_right (Nat.card_pos) hB
      · refine ih (Nat.card (minusPart s U)) ?_ _ rfl (h.isInvariant_minusPart hs hU)
        rw [← hn, hcard]
        exact lt_mul_of_one_lt_left (Nat.card_pos) hA

end Setup

end CFSG.EvenSporadicStandard.M24Std.CResH
