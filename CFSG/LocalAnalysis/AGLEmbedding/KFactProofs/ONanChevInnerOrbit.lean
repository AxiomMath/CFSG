module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.AGLEmbedding

@[expose] def bfsAux (act : ℕ → ℕ → ℕ) : List (ℕ × ℕ) → ℕ → Option ℕ
  | [], m => some m
  | (p, g) :: rest, m => if m.testBit p then bfsAux act rest (m ||| 1 <<< act g p) else none

theorem testBit_or_shiftLeft (m x c : ℕ) :
    (m ||| 1 <<< x).testBit c = (m.testBit c || decide (c = x)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  simp [eq_comm]

theorem bfsAux_sound {R : ℕ → Prop} (act : ℕ → ℕ → ℕ) (hact : ∀ g c, R c → R (act g c)) :
    ∀ (steps : List (ℕ × ℕ)) (m m' : ℕ), (∀ c, m.testBit c = true → R c) →
      bfsAux act steps m = some m' → ∀ c, m'.testBit c = true → R c := by
  intro steps
  induction steps with
  | nil =>
    intro m m' hm h
    simp only [bfsAux, Option.some.injEq] at h
    subst h
    exact hm
  | cons s rest ih =>
    obtain ⟨p, g⟩ := s
    intro m m' hm h
    simp only [bfsAux] at h
    split_ifs at h with hp
    refine ih _ m' (fun c hc => ?_) h
    rw [testBit_or_shiftLeft] at hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | rfl
    · exact hm c hc
    · exact hact g p (hm p hp)

end CFSG.AGLEmbedding
