module

public import Certificates.Data.Kernel.Sp43KOrb
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.Sp43K

theorem tGo_spec {a b a' b' N T e : ℕ} :
    ∀ (R : List (ℕ × ℕ)) (s : ℕ), tGo a b a' b' N T e R s = true →
      e = s + R.length ∧ ∀ i, s ≤ i → i < e →
        i < N ∧ tOne a b a' b' N T i (R.getD (i - s) (0, 0)) = true
  | [], s, h => by
    have h' : (s == e) = true := h
    have hse : s = e := beq_iff_eq.1 h'
    exact ⟨by simp [hse], fun i hi hie => by omega⟩
  | r :: R, s, h => by
    have h' : (Nat.blt s N && tOne a b a' b' N T s r && tGo a b a' b' N T e R (s + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨hsn, hone⟩, hrest⟩ := h'
    obtain ⟨he, hall⟩ := tGo_spec R (s + 1) hrest
    refine ⟨by simp [he]; omega, fun i hi hie => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact ⟨hsn, by simpa using hone⟩
    · obtain ⟨h1, h2⟩ := hall i hlt hie
      refine ⟨h1, ?_⟩
      have : i - s = (i - (s + 1)) + 1 := by omega
      rw [this, List.getD_cons_succ]
      exact h2

theorem inGo_spec {P N T : ℕ} :
    ∀ (R : List ℕ) (s : ℕ), inGo P N T R s = true → ∀ i, s ≤ i → i < s + R.length →
      fldT P i = oneT ∨ (R.getD (i - s) 0 < N ∧ fldT T (R.getD (i - s) 0) = fldT P i)
  | [], s, _ => fun i hi hie => by simp at hie; omega
  | x :: R, s, h => by
    have h' : ((fldT P s == oneT || decide (x < N) && fldT T x == fldT P s) &&
        inGo P N T R (s + 1)) = true := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨hone, hrest⟩ := h'
    intro i hi hie
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · simpa using hone
    · have := inGo_spec R (s + 1) hrest i hlt (by simp at hie; omega)
      have e : i - s = (i - (s + 1)) + 1 := by omega
      rw [e, List.getD_cons_succ]
      exact this

theorem oGo_spec {n₁ n₁' n₂ n₂' k M r X N T D e : ℕ} :
    ∀ (R : List (ℕ × ℕ)) (s : ℕ), oGo n₁ n₁' n₂ n₂' k M r X N T D e R s = true →
      e = s + R.length ∧ ∀ i, s ≤ i → i < e →
        i < N ∧ oOne n₁ n₁' n₂ n₂' k M r X N T D i (R.getD (i - s) (0, 0)) = true
  | [], s, h => by
    have h' : (s == e) = true := h
    have hse : s = e := beq_iff_eq.1 h'
    exact ⟨by simp [hse], fun i hi hie => by omega⟩
  | q :: R, s, h => by
    have h' : (Nat.blt s N && oOne n₁ n₁' n₂ n₂' k M r X N T D s q &&
        oGo n₁ n₁' n₂ n₂' k M r X N T D e R (s + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨hsn, hone⟩, hrest⟩ := h'
    obtain ⟨he, hall⟩ := oGo_spec R (s + 1) hrest
    refine ⟨by simp [he]; omega, fun i hi hie => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact ⟨hsn, by simpa using hone⟩
    · obtain ⟨h1, h2⟩ := hall i hlt hie
      refine ⟨h1, ?_⟩
      have : i - s = (i - (s + 1)) + 1 := by omega
      rw [this, List.getD_cons_succ]
      exact h2

end CFSG.KC.Sp43K

end
