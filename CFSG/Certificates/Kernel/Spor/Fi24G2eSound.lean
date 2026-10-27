module

public import Certificates.Data.Kernel.Spor.Fi24G2e
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound

public section

namespace CFSG.KC.Fi24G2eS

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24G2e CFSG.KC.Fi24FixS

theorem strictN_eqE (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem letB_eqE (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem andB_eqE (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eqE (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem iterWalk_eq (TG : ℕ → ℕ → ℕ) (z : List ℕ) : ∀ (e r : ℕ),
    iterWalk TG z e r = walk TG (List.replicate e z).flatten r
  | 0, r => rfl
  | e + 1, r => by
    change strictN (iterWalk TG z e r) (fun s => walk TG z s) = _
    rw [strictN_eqE, iterWalk_eq TG z e r, List.replicate_succ', List.flatten_append,
      List.flatten_singleton, walk_append]

theorem brayWalk_eq (TG : ℕ → ℕ → ℕ) (w g : List ℕ) (e : ℕ) (odd : Bool) (r : ℕ) :
    brayWalk TG w g e odd r = walk TG (brayWord w g e odd) r := by
  unfold brayWalk brayWord
  rw [walk_append, iterWalk_eq]
  cases odd <;> rfl

theorem permLOK_spec {FL f P : ℕ → ℕ} {m : ℕ} (h : permLOK FL f P m = true) (hm : m ≤ 1024) :
    ∀ i < m, P i < m ∧ f (FL i) = FL (P i) := by
  intro i hi
  have h1 := allBelow_spec h (by omega) i hi
  rw [andB_eqE, Bool.and_eq_true] at h1
  exact ⟨by simpa using h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem invLOK_spec {P Q : ℕ → ℕ} {m : ℕ} (h : invLOK P Q m = true) (hm : m ≤ 1024) :
    ∀ i < m, Q i < m ∧ P (Q i) = i := by
  intro i hi
  have h1 := allBelow_spec h (by omega) i hi
  rw [andB_eqE, Bool.and_eq_true] at h1
  exact ⟨by simpa using h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem cmLOK_spec {A Ai B Bi C : ℕ → ℕ} {m : ℕ} (h : cmLOK A Ai B Bi C m = true) (hm : m ≤ 1024) :
    ∀ i < m, C i = Bi (Ai (B (A i))) := fun i hi =>
  Nat.eq_of_beq_eq_true (allBelow_spec h (by omega) i hi)

theorem cntId_eq (P : ℕ → ℕ) {m : ℕ} (hm : m ≤ 1024) :
    cntId P m = ((Finset.range m).filter fun i => P i = i).card := by
  unfold cntId
  rw [sumBelow_eq _ _ _ (by omega), Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : P i = i
  · rw [if_pos h, show Nat.beq (P i) i = true from Nat.beq_eq_true_eq _ _ ▸ h]
  · have hb : Nat.beq (P i) i = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact h (Nat.eq_of_beq_eq_true hb)
    rw [if_neg h, hb]

theorem clauseOK_spec {FL YL : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {QL : ℕ → List ℕ} {o u0 u1 u2 m : ℕ}
    (h : clauseOK FL TG QL YL o u0 u1 u2 m = true) (hm : m ≤ 1024) :
    ∀ j < m, FL j = u0 ∨ FL j = u1 ∨ FL j = u2 ∨ (walk TG (QL j) o = FL j ∧ YL j < m ∧
      walk TG ((QL j).reverse ++ 0 :: QL j) (FL (YL j)) ≠ FL (YL j)) := by
  intro j hj
  have h1 := allBelow_spec h (by omega) j hj
  unfold clStep at h1
  rw [letB_eqE] at h1
  simp only [orB_eqE, andB_eqE, letB_eqE, Bool.or_eq_true, Bool.and_eq_true] at h1
  rcases h1 with h1 | h1 | h1 | ⟨h2, h3, h4⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
  · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1)))
  · refine Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true h2, by simpa using h3, fun e => ?_⟩))
    rw [e] at h4
    simp at h4

end CFSG.KC.Fi24G2eS

end
