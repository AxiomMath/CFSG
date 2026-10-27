module

public import Certificates.Data.Kernel.Spor.Fi24Kn
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound

public section

namespace CFSG.KC.Fi24KnS

open CFSG.KC.Loop CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24Kn

theorem nthN_eq (l : List ℕ) (i : ℕ) : nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nthN l i = _
      rw [ih]
      rfl

theorem nthW_eq (l : List (List ℕ)) (i : ℕ) : nthW l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nthW l i = _
      rw [ih]
      rfl

private theorem andB_t {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem negB_t {a : Bool} : negB a = true ↔ a = false := by
  cases a <;> decide

private theorem eqB_t {a b : Bool} : eqB a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem bIf_t (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem disjB_t {a b c d : ℕ} : disjB a b c d = true ↔ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  unfold disjB
  rw [negB_t]
  have e : ∀ x y : ℕ, Nat.beq x y = false ↔ x ≠ y := fun x y => by
    cases h : Nat.beq x y
    · exact ⟨fun _ hxy => by rw [hxy, Nat.beq_refl] at h; exact absurd h (by decide),
        fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' (by decide), fun hxy => absurd (Nat.eq_of_beq_eq_true h) hxy⟩
  have o : ∀ x y : Bool, orB x y = false ↔ x = false ∧ y = false := fun x y => by
    cases x <;> cases y <;> decide
  rw [o, o, o, e, e, e, e]

theorem knOK_spec {TG : ℕ → ℕ → ℕ} {FD : ℕ → ℕ} {L A B : ℕ → ℕ} {C : ℕ → List ℕ} {n m : ℕ}
    (h : knOK TG FD L A B C n m = true) (hm : m ≤ 1024) :
    ∀ i < m, ∀ j < m,
      (i = j → walk TG (C i) (L i) = 0 ∧ A i < B i ∧ B i < n) ∧
      (i ≠ j → ¬ (A i = A j ∧ B i = B j) ∧
        (fComp (FD (walk TG (C i) (L j))) = 2 ↔
          A i ≠ A j ∧ A i ≠ B j ∧ B i ≠ A j ∧ B i ≠ B j)) := by
  intro i hi j hj
  have h1 := Fi24FixS.allBelow_spec h (by omega) i hi
  have h2 := Fi24FixS.allBelow_spec h1 (by omega) j hj
  unfold knStep at h2
  rw [bIf_t] at h2
  by_cases hij : i = j
  · subst hij
    rw [if_pos (Nat.beq_refl i)] at h2
    obtain ⟨e1, e2⟩ := andB_t.1 h2
    obtain ⟨e3, e4⟩ := andB_t.1 e2
    exact ⟨fun _ => ⟨Nat.eq_of_beq_eq_true e1, by simpa using e3, by simpa using e4⟩,
      fun h => absurd rfl h⟩
  · have hb : Nat.beq i j = false := by
      cases h : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hij
    rw [if_neg (by rw [hb]; decide)] at h2
    obtain ⟨e1, e2⟩ := andB_t.1 h2
    refine ⟨fun h => absurd h hij, fun _ => ⟨?_, ?_⟩⟩
    · rintro ⟨ha, hb'⟩
      rw [negB_t] at e1
      have : andB (Nat.beq (A i) (A j)) (Nat.beq (B i) (B j)) = true :=
        andB_t.2 ⟨by simpa using ha, by simpa using hb'⟩
      rw [this] at e1
      exact absurd e1 (by decide)
    · rw [eqB_t] at e2
      rw [← disjB_t, ← e2, Nat.beq_eq]

end CFSG.KC.Fi24KnS

end
