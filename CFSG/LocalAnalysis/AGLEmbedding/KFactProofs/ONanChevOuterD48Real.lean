module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Pair

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

structure Realization (X : Type) [Group X] where
  Rep : Pr → X → Prop
  rep_one : Rep oneP 1
  rep_mul : ∀ {p q : Pr} {x y : X}, Rep p x → Rep q y → Rep (mulP p q) (x * y)
  rep_ext : ∀ {p q : Pr} {x y : X}, Rep p x → Rep q y → p = q → x = y
  rep_id : ∀ {p : Pr}, Rep p 1 → p = oneP
  letter : ℕ → X
  rep_letter : ∀ {k : ℕ}, k < 24 → Rep (symP k) (letter k)
  phi : X
  rep_phi : Rep (symP 24) phi

namespace Realization

variable {X : Type} [Group X] (R : Realization X)

@[expose] def elt (s : ℕ) : X := if s < 24 then R.letter s else R.phi

theorem symP_of_ge {s : ℕ} (h : 24 ≤ s) : symP s = symP 24 := by
  simp [symP, not_lt.2 h]

theorem rep_sym (s : ℕ) : R.Rep (symP s) (R.elt s) := by
  unfold elt
  split_ifs with h
  · exact R.rep_letter h
  · rw [symP_of_ge (not_lt.1 h)]
    exact R.rep_phi

@[expose] def wordElt (w : List ℕ) : X := (w.map R.elt).prod

theorem rep_word (w : List ℕ) : R.Rep (wordP w) (R.wordElt w) := by
  induction w with
  | nil => exact R.rep_one
  | cons s w ih =>
    simp only [wordP, List.foldr_cons, wordElt, List.map_cons, List.prod_cons]
    exact R.rep_mul (R.rep_sym s) ih

theorem rep_pow {p : Pr} {x : X} (hp : R.Rep p x) (n : ℕ) : R.Rep (powP p n) (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact R.rep_one
  | succ n ih =>
    rw [pow_succ']
    exact R.rep_mul hp ih

end Realization

end CFSG.AGLEmbedding.ChevOuterD48
