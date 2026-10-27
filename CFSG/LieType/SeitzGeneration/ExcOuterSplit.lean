module

public import CFSG.LieType.SeitzGeneration.ExcOuterClasses

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley TauCeti

@[expose] def EqTwoRange (c : PrimePower → LieTypeIndex) (X : PrimePower → Prop) (a : ℕ → ℕ) :
    LieTypeIndex → ℕ → Prop :=
  fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = c q ∧ X q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) = 2

@[expose] def LeOneRange (c : PrimePower → LieTypeIndex) (X : PrimePower → Prop) (a : ℕ → ℕ) :
    LieTypeIndex → ℕ → Prop :=
  fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = c q ∧ X q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1

theorem seitzExcOuterNarrowForAt_leTwo_of_split {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {a : ℕ → ℕ}
    (h₂ : SeitzExcOuterNarrowForAt F (EqTwoRange c X a))
    (h₁ : SeitzExcOuterNarrowForAt F (LeOneRange c X a)) :
    SeitzExcOuterNarrowForAt F (LeTwoRange c X a) :=
  SeitzExcOuterNarrowForAt.union (fun d p _ _ hQ => by
    obtain ⟨hp5, q, hdq, hX, hle⟩ := hQ
    by_cases h : a (orderOf ((q.card : ℕ) : ZMod p)) = 2
    · exact Or.inl ⟨hp5, q, hdq, hX, h⟩
    · exact Or.inr ⟨hp5, q, hdq, hX, by omega⟩) h₂ h₁

@[expose] def SeitzExcOuterNarrowF4EqTwo : Prop :=
  SeitzExcOuterNarrowForAt IsF4Index
    (EqTwoRange LieTypeIndex.F4 (fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (degCount Tag.F4))

@[expose] def SeitzExcOuterNarrowF4LeOne : Prop :=
  SeitzExcOuterNarrowForAt IsF4Index
    (LeOneRange LieTypeIndex.F4 (fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (degCount Tag.F4))

@[expose] def SeitzExcOuterNarrowE6EqTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE6Index (EqTwoRange LieTypeIndex.E6 (fun _ => True) (degCount Tag.E6))

@[expose] def SeitzExcOuterNarrowE6LeOne : Prop :=
  SeitzExcOuterNarrowForAt IsE6Index (LeOneRange LieTypeIndex.E6 (fun _ => True) (degCount Tag.E6))

@[expose] def SeitzExcOuterNarrowE7EqTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE7Index (EqTwoRange LieTypeIndex.E7 (fun _ => True) (degCount Tag.E7))

@[expose] def SeitzExcOuterNarrowE7LeOne : Prop :=
  SeitzExcOuterNarrowForAt IsE7Index (LeOneRange LieTypeIndex.E7 (fun _ => True) (degCount Tag.E7))

@[expose] def SeitzExcOuterNarrowE8EqTwo : Prop :=
  SeitzExcOuterNarrowForAt IsE8Index (EqTwoRange LieTypeIndex.E8 (fun _ => True) (degCount Tag.E8))

@[expose] def SeitzExcOuterNarrowE8LeOne : Prop :=
  SeitzExcOuterNarrowForAt IsE8Index (LeOneRange LieTypeIndex.E8 (fun _ => True) (degCount Tag.E8))

@[expose] def SeitzExcOuterNarrowTwistedE6EqTwo : Prop :=
  SeitzExcOuterNarrowForAt IsTwistedE6Index
    (EqTwoRange LieTypeIndex.twistedE6 (fun _ => True) degCountTw)

@[expose] def SeitzExcOuterNarrowTwistedE6LeOne : Prop :=
  SeitzExcOuterNarrowForAt IsTwistedE6Index
    (LeOneRange LieTypeIndex.twistedE6 (fun _ => True) degCountTw)

end CFSG.LieType.SeitzGeneration
