module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

theorem exists_ne_one_mem_ker_of_cyclic {G H : Type*} [Group G] [Group H] [Finite H] [IsCyclic H]
    (f : G →* H) {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) : ∃ x ∈ E, x ≠ 1 ∧ f x = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype H := Fintype.ofFinite H
  let g : E → {h : H // h ^ p = 1} := fun x =>
    ⟨f x, by rw [← map_pow]; simp [hE x x.2]⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : f (x : G) = f (y : G) := congrArg Subtype.val hxy
    have h2 : f ((x : G) * (y : G)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    by_contra hne
    have hne' : (x : G) * (y : G)⁻¹ ≠ 1 := by
      intro h
      exact hne (Subtype.ext (mul_inv_eq_one.mp h))
    exact hcon _ (E.mul_mem x.2 (E.inv_mem y.2)) hne' h2
  have hle : Nat.card E ≤ Nat.card {h : H // h ^ p = 1} := Nat.card_le_card_of_injective g hg
  have hle2 : Nat.card {h : H // h ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have hp1 := hp.one_lt
  have h2 : p ^ 2 ≤ p := hcard ▸ hle.trans hle2
  have h3 : p * p ≤ p * 1 := by simpa [pow_two] using h2
  have := Nat.le_of_mul_le_mul_left h3 hp.pos
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
