module

public import Aesop.BuiltinRules
public import Batteries.Data.List.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ToAdditive

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Chain

variable {α : Type} (val : α → ℕ) (ok : α → Bool)

@[expose] def chainChk : ℕ → List α → Bool
  | _, [] => true
  | prev, a :: rs => decide (prev < val a) && ok a && chainChk (val a) rs

@[expose] def lastV : ℕ → List α → ℕ
  | prev, [] => prev
  | _, a :: rs => lastV (val a) rs

@[expose] def chainTo : ℕ → ℕ → List α → Bool
  | prev, fin, [] => prev == fin
  | prev, fin, a :: rs => decide (prev < val a) && ok a && chainTo (val a) fin rs

theorem chainTo_iff : ∀ (rows : List α) (prev fin : ℕ),
    chainTo val ok prev fin rows = true →
      chainChk val ok prev rows = true ∧ lastV val prev rows = fin
  | [], prev, fin, h => ⟨rfl, beq_iff_eq.1 h⟩
  | a :: rs, prev, fin, h => by
    simp only [chainTo, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := chainTo_iff rs (val a) fin h3
    refine ⟨?_, this.2⟩
    simp only [chainChk, Bool.and_eq_true]
    exact ⟨⟨h1, h2⟩, this.1⟩

theorem chainChk_append : ∀ (rs ss : List α) (prev : ℕ),
    chainChk val ok prev (rs ++ ss) = true ↔
      chainChk val ok prev rs = true ∧ chainChk val ok (lastV val prev rs) ss = true
  | [], ss, prev => by simp [chainChk, lastV]
  | a :: rs, ss, prev => by
    simp only [List.cons_append, chainChk, lastV, Bool.and_eq_true]
    rw [chainChk_append rs ss (val a)]
    exact and_assoc.symm

theorem chainChk_chunk (rs ss : List α) (prev fin : ℕ) (h : chainTo val ok prev fin rs = true)
    (h2 : chainChk val ok fin ss = true) : chainChk val ok prev (rs ++ ss) = true := by
  obtain ⟨h1, h3⟩ := chainTo_iff val ok rs prev fin h
  exact (chainChk_append val ok rs ss prev).2 ⟨h1, by rw [h3]; exact h2⟩

theorem chainChk_sound : ∀ (rows : List α) (prev : ℕ), chainChk val ok prev rows = true →
    (∀ a ∈ rows, ok a = true) ∧ (rows.map val).Pairwise (· < ·) ∧
      prev ≤ lastV val prev rows ∧ ∀ a ∈ rows, prev < val a
  | [], prev, _ => ⟨by simp, by simp, le_refl _, by simp⟩
  | a :: rs, prev, h => by
    simp only [chainChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2, ih3, ih4⟩ := chainChk_sound rs (val a) h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h2
      · exact ih1 r' hr'
    · refine List.pairwise_cons.2 ⟨?_, ih2⟩
      intro v hv
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hv
      exact ih4 r' hr'
    · exact le_trans h1.le ih3
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h1
      · exact lt_trans h1 (ih4 r' hr')

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Chain
