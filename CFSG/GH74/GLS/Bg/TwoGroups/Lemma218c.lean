module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Subgroup

structure Ctx (E : Type) [CommGroup E] [Finite E] (X : Subgroup (MulAut E)) (S : Sylow 2 ↥X) :
    Prop where
  h2 : ∀ e : E, e * e = 1
  hE : Nat.card E = 16
  hS2 : ∀ s ∈ (S : Subgroup ↥X), s * s = 1
  hS4 : Nat.card (S : Subgroup ↥X) = 4
  hC : Nat.card {e : E // ∀ s ∈ (S : Subgroup ↥X), (s : MulAut E) e = e} = 2

@[expose] def fixS {E : Type} [CommGroup E] {X : Subgroup (MulAut E)} (T : Subgroup ↥X) :
    Subgroup E where
  carrier := {e | ∀ s ∈ T, (s : MulAut E) e = e}
  one_mem' := fun s _ => map_one _
  mul_mem' := fun {a b} (ha : ∀ s ∈ T, (s : MulAut E) a = a)
      (hb : ∀ s ∈ T, (s : MulAut E) b = b) s hs => by
    rw [map_mul, ha s hs, hb s hs]
  inv_mem' := fun {a} (ha : ∀ s ∈ T, (s : MulAut E) a = a) s hs => by
    rw [map_inv, ha s hs]

section Ctx

variable {E : Type} [CommGroup E] [Finite E] {X : Subgroup (MulAut E)} {S : Sylow 2 ↥X}

theorem Ctx.comm (c : Ctx E X S) {a b : ↥X} (ha : a ∈ (S : Subgroup ↥X))
    (hb : b ∈ (S : Subgroup ↥X)) : a * b = b * a := by
  have hab : a * b ∈ (S : Subgroup ↥X) := mul_mem ha hb
  have h1 := c.hS2 _ hab
  have h2 := c.hS2 a ha
  have h3 := c.hS2 b hb
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]

theorem Ctx.isKleinFour (c : Ctx E X S) : IsKleinFour (S : Subgroup ↥X) := by
  refine ⟨c.hS4, ?_⟩
  have : Nontrivial (S : Subgroup ↥X) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [c.hS4]; norm_num)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (c.hS2 g g.2)) hg

theorem Ctx.mem_cases (c : Ctx E X S) {s t : ↥X} (hs : s ∈ (S : Subgroup ↥X))
    (ht : t ∈ (S : Subgroup ↥X)) (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) {r : ↥X}
    (hr : r ∈ (S : Subgroup ↥X)) : r = 1 ∨ r = s ∨ r = t ∨ r = s * t := by
  have := c.isKleinFour
  by_cases h1 : r = 1
  · exact Or.inl h1
  by_cases h2 : r = s
  · exact Or.inr (Or.inl h2)
  by_cases h3 : r = t
  · exact Or.inr (Or.inr (Or.inl h3))
  right; right; right
  have := IsKleinFour.eq_mul_of_ne_all (G := (S : Subgroup ↥X)) (x := ⟨s, hs⟩) (y := ⟨t, ht⟩)
    (z := ⟨r, hr⟩) (fun h => hs1 (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h))
    (fun h => hst (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem Ctx.exists_other (c : Ctx E X S) (s : ↥X) :
    ∃ t ∈ (S : Subgroup ↥X), t ≠ 1 ∧ t ≠ s := by
  classical
  by_contra hcon
  have hall : ∀ t ∈ (S : Subgroup ↥X), t = 1 ∨ t = s := by
    intro t ht
    by_contra h
    exact hcon ⟨t, ht, fun h1 => h (Or.inl h1), fun h1 => h (Or.inr h1)⟩
  have hle : Nat.card (S : Subgroup ↥X) ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective
      (fun t : (S : Subgroup ↥X) => decide ((t : ↥X) = 1)) ?_
    intro a b hab
    rcases hall a a.2 with ha | ha <;> rcases hall b b.2 with hb | hb
    · exact Subtype.ext (ha.trans hb.symm)
    · by_cases hs1 : s = 1
      · exact Subtype.ext (ha.trans (hb.trans hs1).symm)
      · simp [ha, hb, hs1] at hab
    · by_cases hs1 : s = 1
      · exact Subtype.ext ((ha.trans hs1).trans hb.symm)
      · simp [ha, hb, hs1] at hab
    · exact Subtype.ext (ha.trans hb.symm)
  have := c.hS4
  simp at hle
  omega

theorem Ctx.card_fixS (c : Ctx E X S) : Nat.card (fixS (S : Subgroup ↥X)) = 2 := by
  exact (Nat.card_congr (Equiv.refl _ : fixS (S : Subgroup ↥X) ≃
    {e : E // ∀ s ∈ (S : Subgroup ↥X), (s : MulAut E) e = e})).trans c.hC

theorem Ctx.free (c : Ctx E X S) {s : ↥X} (hs : s ∈ (S : Subgroup ↥X)) (hs1 : s ≠ 1) :
    Nat.card (fixE (s : MulAut E)) = 4 := by
  obtain ⟨t, ht, ht1, hts⟩ := c.exists_other s
  have hss : (s : MulAut E) * (s : MulAut E) = 1 := congrArg Subtype.val (c.hS2 s hs)
  have htt : (t : MulAut E) * (t : MulAut E) = 1 := congrArg Subtype.val (c.hS2 t ht)
  have hst : (s : MulAut E) * (t : MulAut E) = (t : MulAut E) * (s : MulAut E) :=
    congrArg Subtype.val (c.comm hs ht)
  have hs1' : (s : MulAut E) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hint : Nat.card ↥(fixE (s : MulAut E) ⊓ fixE (t : MulAut E)) = 2 := by
    have : fixE (s : MulAut E) ⊓ fixE (t : MulAut E) = fixS (S : Subgroup ↥X) := by
      ext e
      constructor
      · rintro ⟨hes, het⟩ r hr
        have hes' := (mem_fixE _ _).mp hes
        have het' := (mem_fixE _ _).mp het
        rcases c.mem_cases hs ht hs1 ht1 (Ne.symm hts) hr with rfl | rfl | rfl | rfl
        · exact rfl
        · exact hes'
        · exact het'
        · show ((s * t : ↥X) : MulAut E) e = e
          rw [Subgroup.coe_mul, MulAut.mul_apply, het', hes']
      · intro he
        exact ⟨(mem_fixE _ _).mpr (he s hs), (mem_fixE _ _).mpr (he t ht)⟩
    rw [this]
    exact c.card_fixS
  exact fixE_card_four c.h2 c.hE _ _ hss htt hst hs1' hint

theorem Ctx.exists_e0 (c : Ctx E X S) : ∃ e₀ : E, e₀ ≠ 1 ∧ e₀ ∈ fixS (S : Subgroup ↥X) ∧
    ∀ e ∈ fixS (S : Subgroup ↥X), e = 1 ∨ e = e₀ := by
  have hcard := c.card_fixS
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : fixS (S : Subgroup ↥X))).mp hcard
  refine ⟨y.1, fun h => hy (Subtype.ext h), y.2, ?_⟩
  intro e he
  by_cases h1 : e = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨e, he⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

end Ctx

section Z1

local instance instDecEqZ2xS3 : DecidableEq Z2xS3 := inferInstance
local instance instFintypeZ2xS3 : Fintype Z2xS3 := inferInstance

theorem z1_check : ∀ a b g : Z2xS3, a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 →
    a ≠ b → g * a = a * g → g * b = b * g → g * g = 1 := by
  decide +kernel

end Z1

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
