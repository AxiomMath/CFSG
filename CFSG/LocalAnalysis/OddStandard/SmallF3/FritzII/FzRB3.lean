module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private lemma fzrAux_card_invol :
    Nat.card {a : Multiplicative (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2) // a * a = 1} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem fzr_B_omega {G : Type} [Group G] {P : Subgroup G}
    (e : ↥P ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2)) :
    (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧
      ∃ X : Subgroup G, X ≤ P ∧ (∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) ∧ Nat.card X = 16 := by
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have h : (⟨a, ha⟩ : ↥P) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    simpa using congrArg Subtype.val h
  let X : Subgroup G :=
    { carrier := {x | x ∈ P ∧ x * x = 1}
      one_mem' := ⟨P.one_mem, mul_one 1⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨P.mul_mem ha.1 hb.1, ?_⟩
        have hab : b * a = a * b := (hcomm a ha.1 b hb.1).symm
        calc (a * b) * (a * b) = a * (b * a) * b := by
              rw [mul_assoc a b (a * b), ← mul_assoc b a b, mul_assoc a (b * a) b]
          _ = a * (a * b) * b := by rw [hab]
          _ = (a * a) * (b * b) := by rw [← mul_assoc a a b, ← mul_assoc]
          _ = 1 := by rw [ha.2, hb.2, one_mul]
      inv_mem' := by
        intro a ha
        refine ⟨P.inv_mem ha.1, ?_⟩
        rw [← mul_inv_rev, ha.2, inv_one] }
  refine ⟨hcomm, X, fun x hx => hx.1, fun x => Iff.rfl, ?_⟩
  have hsq : ∀ x : ↥P, x.1 * x.1 = 1 ↔ x * x = 1 := by
    intro x
    rw [Subtype.ext_iff]
    rfl
  have he : ∀ x : ↥P, x * x = 1 ↔ e x * e x = 1 := by
    intro x
    constructor
    · intro hx; rw [← map_mul, hx, map_one]
    · intro hx; exact e.injective (by rw [map_mul, hx, map_one])
  have hcard :
      Nat.card X =
        Nat.card {a : Multiplicative (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2) // a * a = 1} :=
    Nat.card_congr <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ P) (fun x => x * x = 1)).symm.trans <|
        (Equiv.subtypeEquivRight hsq).trans (Equiv.subtypeEquiv e.toEquiv he)
  exact hcard.trans fzrAux_card_invol

end CFSG.OddStandard.SmallF3.FritzII
