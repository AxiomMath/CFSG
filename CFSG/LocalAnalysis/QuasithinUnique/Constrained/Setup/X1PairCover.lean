module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Cover

variable {S : Type} [Group S] [DecidableEq S]

@[expose] def coverMapG (key : S → ℕ) (Rl : List S) (reps : List (S × S)) :
    Std.HashMap (ℕ × ℕ) (ℕ × ℕ) :=
  reps.zipIdx.foldl (fun m tk =>
    Rl.zipIdx.foldl (fun m rr =>
      m.insertIfNew (key (rr.1⁻¹ * tk.1.1 * rr.1), key (rr.1⁻¹ * tk.1.2 * rr.1)) (tk.2, rr.2)) m) {}

@[expose] def coveredG (key : S → ℕ) (Rl : List S) (reps : List (S × S))
    (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (q : S × S) : Bool :=
  match m[(key q.1, key q.2)]? with
  | some (k, ri) =>
    decide (k < reps.length) && decide (ri < Rl.length) &&
      (Rl.getD ri 1 * q.1 * (Rl.getD ri 1)⁻¹ == (reps.getD k (1, 1)).1) &&
      (Rl.getD ri 1 * q.2 * (Rl.getD ri 1)⁻¹ == (reps.getD k (1, 1)).2)
  | none => false

theorem coveredG_sound (key : S → ℕ) (Rl : List S) (reps : List (S × S))
    (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (q : S × S) (h : coveredG key Rl reps m q = true) :
    ∃ t ∈ reps, ∃ r ∈ Rl, r * q.1 * r⁻¹ = t.1 ∧ r * q.2 * r⁻¹ = t.2 := by
  unfold coveredG at h
  split at h
  · rename_i k ri hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hk', hri⟩, h1⟩, h2⟩ := h
    refine ⟨reps.getD k (1, 1), ?_, Rl.getD ri 1, ?_, h1, h2⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      exact List.getElem_mem hk'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri]
      exact List.getElem_mem hri
  · simp at h

@[expose] def g2coverBad (key : S → ℕ) (Rl : List S) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) :
    List (S × S) :=
  let reps := G2.map fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)
  let m := coverMapG key Rl reps
  (pairG (invG Rl)).filter fun q => !coveredG key Rl reps m q

theorem gen2_hyps_fast (key : S → ℕ) (Rl : List S) (conj : List (List ℤ) → List S)
    (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) {p : ℕ} [Fact p.Prime]
    (hok : g2ok Rl conj G2 p = true) (hconj : ∀ ws, (conj ws).length = ws.length) :
    (∀ q ∈ pairG (invG Rl), q ∈ g2coverBad key Rl G2 ∨
      ∃ t ∈ G2.map (fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)), ∃ r ∈ Rl,
        r * q.1 * r⁻¹ = t.1 ∧ r * q.2 * r⁻¹ = t.2) ∧
    (∀ t ∈ G2.map (fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)), ∃ cs : List S, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t.1, t.2}), orderOf x = p) := by
  refine ⟨fun q hq => ?_, g2ok_wit Rl conj G2 hok hconj⟩
  by_cases hc : coveredG key Rl (G2.map fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1))
      (coverMapG key Rl (G2.map fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1))) q = true
  · exact Or.inr (coveredG_sound _ _ _ _ _ hc)
  · exact Or.inl (by
      unfold g2coverBad
      simp only [List.mem_filter]
      exact ⟨hq, by simpa using hc⟩)

end Cover

end CFSG.QuasithinUnique.Setup.X1
