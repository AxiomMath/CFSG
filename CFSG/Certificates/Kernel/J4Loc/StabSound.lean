module

public import CFSG.Certificates.Kernel.J4Loc.TrioOctSound
public import Certificates.Data.Kernel.J4Loc.Stab

public section

namespace CFSG.KS.J4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.Loop CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem wordAct_eq (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) :
    ∀ w : List ℕ, (∀ l ∈ w, l < 6) → ∀ x : ℕ,
      wordAct letterRows w x = (w.map fun l => letters.getD l 0).foldr act x := by
  intro w
  induction w with
  | nil => intro _ x; rfl
  | cons l w ih =>
    intro hw x
    have e : wordAct letterRows (l :: w) x = actK (rowL letterRows l) (wordAct letterRows w x) :=
      rfl
    rw [e, List.map_cons, List.foldr_cons, ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)),
      ← act_eq_actK hLR (hw l List.mem_cons_self)]

theorem stabOK_spec {LR : List (List ℕ)} :
    ∀ {S : List (ℕ × ℕ × ℕ × List ℕ)}, stabOK LR S = true → ∀ e ∈ S, stabRowOK LR e = true
  | [], _, _, he => absurd he List.not_mem_nil
  | e' :: S, h, e, he => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact stabOK_spec h2 e he

theorem stabHas_spec {a b c : ℕ} :
    ∀ {S : List (ℕ × ℕ × ℕ × List ℕ)}, stabHas S a b c = true → ∃ w, (a, b, c, w) ∈ S
  | [], h => absurd h Bool.false_ne_true
  | ⟨a', b', c', w⟩ :: S, h => by
    rcases orB_true h with h | h
    · obtain ⟨h1, h⟩ := andB_true h
      obtain ⟨h2, h3⟩ := andB_true h
      have e1 : a' = a := Nat.eq_of_beq_eq_true h1
      have e2 : b' = b := Nat.eq_of_beq_eq_true h2
      have e3 : c' = c := Nat.eq_of_beq_eq_true h3
      subst e1 e2 e3
      exact ⟨w, List.mem_cons_self⟩
    · obtain ⟨w', hw'⟩ := stabHas_spec h
      exact ⟨w', List.mem_cons_of_mem _ hw'⟩

theorem not_beq {x y : ℕ} (h : x ≠ y) (h' : Nat.beq x y = true) : False :=
  h (Nat.eq_of_beq_eq_true h')

theorem stabCov_spec {V : List ℕ} {S : List (ℕ × ℕ × ℕ × List ℕ)} (h : stabCov V S = true)
    {a b c : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (h1 : a ≠ 0) (h2 : b ≠ 0) (h3 : b ≠ a)
    (h4 : c ≠ 0) (h5 : c ≠ a) (h6 : c ≠ b) (h7 : c ≠ a ^^^ b) : ∃ w, (a, b, c, w) ∈ S := by
  have h := allL_spec (allL_spec (allL_spec h a ha) b hb) c hc
  rcases orB_true h with h | h
  · exact (not_beq h1 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h2 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h3 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h4 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h5 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h6 h).elim
  rcases orB_true h with h | h
  · exact (not_beq h7 h).elim
  exact stabHas_spec h

theorem stab_word (hLR : ∀ l < 6, (letterRows.getD l []).length = 11)
    {S : List (ℕ × ℕ × ℕ × List ℕ)} (hok : stabOK letterRows S = true)
    (hcov : stabCov [0, 422, 553, 911, 1131, 1485, 1602, 2020] S = true) :
    ∀ a ∈ V0F, ∀ b ∈ V0F, ∀ c ∈ V0F, a ≠ 0 → b ≠ 0 → b ≠ a → c ≠ 0 → c ≠ a → c ≠ b →
      c ≠ a ^^^ b → ∃ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) ∧
        w.foldr act 422 = a ∧ w.foldr act 553 = b ∧ w.foldr act 1131 = c := by
  intro a ha b hb c hc h1 h2 h3 h4 h5 h6 h7
  have hV : ∀ x ∈ V0F, x ∈ [0, 422, 553, 911, 1131, 1485, 1602, 2020] := by
    intro x hx
    simpa [V0F] using hx
  obtain ⟨w, hw⟩ := stabCov_spec hcov (hV a ha) (hV b hb) (hV c hc) h1 h2 h3 h4 h5 h6 h7
  obtain ⟨hl, hr⟩ := andB_true (stabOK_spec hok _ hw)
  obtain ⟨ea, hr⟩ := andB_true hr
  obtain ⟨eb, ec⟩ := andB_true hr
  have hl' : ∀ l ∈ w, l < 6 := fun l h => Nat.blt_eq.mp (allL_spec hl l h)
  refine ⟨w.map fun l => letters.getD l 0, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hℓ
    have := hl' l hl
    interval_cases l <;> decide
  · rw [← wordAct_eq hLR w hl']
    exact Nat.eq_of_beq_eq_true ea
  · rw [← wordAct_eq hLR w hl']
    exact Nat.eq_of_beq_eq_true eb
  · rw [← wordAct_eq hLR w hl']
    exact Nat.eq_of_beq_eq_true ec

end CFSG.KS.J4Loc

end
