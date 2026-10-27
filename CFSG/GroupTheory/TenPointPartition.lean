module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.GroupTheory

theorem partition_of_card_ten {V : Type*} [Fintype V]
    (comm : V → V → Prop)
    (hsymm : ∀ a b : V, comm a b → comm b a)
    (hcard : Nat.card V = 10)
    (hdeg : ∀ v : V, Nat.card {w : V // w ≠ v ∧ comm v w} = 3)
    (A B : Set V) (hcover : A ∪ B = Set.univ)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, comm a b) :
    A = ∅ ∨ B = ∅ := by
  classical
  have hFV : Fintype.card V = 10 := by simpa [Nat.card_eq_fintype_card] using hcard
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hall : ∀ y : V, y ≠ x → comm x y := by
      intro y hyx
      have hy : y ∈ A ∪ B := by rw [hcover]; exact Set.mem_univ y
      rcases (by simpa only [Set.mem_union] using hy) with hyA | hyB
      · exact hsymm y x (hAB y hyA x hxB)
      · exact hAB x hxA y hyB
    have hle : Nat.card {y : V // y ≠ x} ≤ Nat.card {y : V // y ≠ x ∧ comm x y} := by
      apply Nat.card_le_card_of_injective
        (fun y : {y : V // y ≠ x} =>
          (⟨y.1, y.2, hall y.1 y.2⟩ : {y : V // y ≠ x ∧ comm x y}))
      intro y z h
      exact Subtype.ext (congrArg (fun w : {w : V // w ≠ x ∧ comm x w} => w.1) h)
    have h9 : Nat.card {y : V // y ≠ x} = 9 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun y : V => y = x),
        Fintype.card_subtype_eq]
      omega
    have h3 := hdeg x
    omega
  rcases Set.eq_empty_or_nonempty A with hA | ⟨a, ha⟩
  · exact Or.inl hA
  rcases Set.eq_empty_or_nonempty B with hB | ⟨b, hb⟩
  · exact Or.inr hB
  have haB : a ∉ B := fun h => (Set.disjoint_left.mp hdisj ha h)
  have hbA : b ∉ A := fun h => (Set.disjoint_left.mp hdisj h hb)
  have hAcard : Nat.card A ≤ 3 := by
    calc Nat.card A ≤ Nat.card {w : V // w ≠ b ∧ comm b w} := by
          apply Nat.card_le_card_of_injective
            (fun y : A => (⟨y.1, (fun h => hbA (h ▸ y.2)), hsymm y.1 b (hAB y.1 y.2 b hb)⟩ :
              {w : V // w ≠ b ∧ comm b w}))
          intro y z h
          exact Subtype.ext (congrArg (fun w : {w : V // w ≠ b ∧ comm b w} => w.1) h)
      _ = 3 := hdeg b
  have hBcard : Nat.card B ≤ 3 := by
    calc Nat.card B ≤ Nat.card {w : V // w ≠ a ∧ comm a w} := by
          apply Nat.card_le_card_of_injective
            (fun y : B => (⟨y.1, (fun h => haB (h ▸ y.2)), hAB a ha y.1 y.2⟩ :
              {w : V // w ≠ a ∧ comm a w}))
          intro y z h
          exact Subtype.ext (congrArg (fun w : {w : V // w ≠ a ∧ comm a w} => w.1) h)
      _ = 3 := hdeg a
  have hsum : Nat.card A + Nat.card B = 10 := by
    have h := Set.ncard_union_eq (s := A) (t := B) hdisj
    rw [hcover, Set.ncard_univ] at h
    rw [Nat.card_coe_set_eq A, Nat.card_coe_set_eq B]
    omega
  omega

end CFSG.GroupTheory
