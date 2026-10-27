module

public import CFSG.GH74.KGroups.PermCheck
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.GH74.KGroups

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def sqOneCheck (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun x => decide (x ^ 2 = 1)

theorem sqOneCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : sqOneCheck (elemsT Q) = true) : ∀ x ∈ Q.originalSubgroup, x ^ 2 = 1 := by
  intro x hx
  simpa using List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx)

theorem getD_mem_of_gens (S : List (Equiv.Perm (Fin n))) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ g ∈ S, g ∈ H) (k : ℕ) : S.getD k 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases h : S[k]? with
  | none => simp
  | some g => exact hH g (List.mem_of_getElem? h)

theorem evalCodes_mem_of_gens (S : List (Equiv.Perm (Fin n))) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ g ∈ S, g ∈ H) (w : List ℤ) : evalCodes S w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons z w ih =>
    simp only [evalCodes]
    refine H.mul_mem ?_ ih
    split_ifs
    · exact getD_mem_of_gens S H hH _
    · exact H.inv_mem (getD_mem_of_gens S H hH _)

@[expose] def conjWordsCheck (S : List (Equiv.Perm (Fin n))) (e0 : Equiv.Perm (Fin n))
    (cws : List (List ℤ)) (LE : List (Equiv.Perm (Fin n))) : Bool :=
  LE.all fun x => decide (x = 1) ||
    cws.any fun w => decide (evalCodes S w * e0 * (evalCodes S w)⁻¹ = x)

theorem conjWordsCheck_sound (S : List (Equiv.Perm (Fin n))) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ g ∈ S, g ∈ H) {e0 : Equiv.Perm (Fin n)} {cws : List (List ℤ)}
    {LE : List (Equiv.Perm (Fin n))} (h : conjWordsCheck S e0 cws LE = true) :
    ∀ x ∈ LE, x ≠ 1 → ∃ g ∈ H, g * e0 * g⁻¹ = x := by
  intro x hx hx1
  have h1 := List.all_eq_true.1 h x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h1
  rcases h1 with h1 | ⟨w, -, hw⟩
  · exact absurd h1 hx1
  · exact ⟨evalCodes S w, evalCodes_mem_of_gens S H hH w, hw⟩

theorem conj_of_words (S : List (Equiv.Perm (Fin n))) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ g ∈ S, g ∈ H) (QE : RawSchreierDatum n) (hQE : ValidSchreier QE)
    {e0 : Equiv.Perm (Fin n)} {cws : List (List ℤ)}
    (h : conjWordsCheck S e0 cws (elemsT QE) = true) :
    ∀ x ∈ QE.originalSubgroup, x ≠ 1 → ∃ g ∈ H, g * e0 * g⁻¹ = x := fun x hx hx1 =>
  conjWordsCheck_sound S H hH h x ((mem_elemsT QE hQE x).2 hx) hx1

@[expose] def indepCheck (e1 e2 e3 : Equiv.Perm (Fin n)) : Bool :=
  decide (e1 ≠ 1 ∧ e2 ≠ 1 ∧ e3 ≠ 1 ∧ e1 * e2 ≠ 1 ∧ e1 * e3 ≠ 1 ∧ e2 * e3 ≠ 1 ∧
    e1 * (e2 * e3) ≠ 1)

theorem indepCheck_sound {e1 e2 e3 : Equiv.Perm (Fin n)} (h : indepCheck e1 e2 e3 = true) :
    e1 ≠ 1 ∧ e2 ≠ 1 ∧ e3 ≠ 1 ∧ e1 * e2 ≠ 1 ∧ e1 * e3 ≠ 1 ∧ e2 * e3 ≠ 1 ∧
      e1 * (e2 * e3) ≠ 1 := by
  simpa [indepCheck] using h

end CFSG.GH74.KGroups
