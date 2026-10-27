module

public import Certificates.Data.Kernel.Fi23P.Defs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.Fi23P

open CFSG.KC.Enum CFSG.KS.Raw.Orb

theorem gOK_iff (k : Nat) : gOK k = true ↔ k < 10 ∧ k ≠ 8 := by
  unfold gOK
  rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e => by rw [e] at h2; exact absurd h2 (by decide)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases e : Nat.beq k 8
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h2

theorem nbrOK_spec {T : Nat → Nat → Nat} {lab pos : Nat → Nat} {c ky k y : Nat}
    (h : nbrOK T lab pos c ky k y = true) : lab (T k y) = c ∧ ky ≤ 16 * pos (T k y) + k := by
  unfold nbrOK at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.le_of_ble_eq_true h.2⟩

theorem nbrsOK_spec {T : Nat → Nat → Nat} {lab pos : Nat → Nat} {c ky y : Nat}
    (h : nbrsOK T lab pos c ky y = true) {k : Nat} (hk : gOK k = true) :
    lab (T k y) = c ∧ ky ≤ 16 * pos (T k y) + k := by
  unfold nbrsOK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h9⟩ := h
  obtain ⟨hk1, hk2⟩ := (gOK_iff k).1 hk
  interval_cases k
  · exact nbrOK_spec h0
  · exact nbrOK_spec h1
  · exact nbrOK_spec h2
  · exact nbrOK_spec h3
  · exact nbrOK_spec h4
  · exact nbrOK_spec h5
  · exact nbrOK_spec h6
  · exact nbrOK_spec h7
  · exact absurd rfl hk2
  · exact nbrOK_spec h9

@[expose] def BfsFacts (T : Nat → Nat → Nat) (rt off lab gen par pos pts : Nat → Nat) (y : Nat) :
    Prop :=
  pos (pts y) = y ∧ pts (pos y) = y ∧ lab y < 3 ∧ off (lab y) ≤ pos y ∧ pos y < off (lab y + 1) ∧
    (∀ k, gOK k = true → lab (T k y) = lab y) ∧
    (pos y = off (lab y) → y = rt (lab y) ∧ par y = 0 ∧ gen y = 0) ∧
    (pos y ≠ off (lab y) → gOK (gen y) = true ∧ par y < 31671 ∧ lab (par y) = lab y ∧
      T (gen y) (par y) = y ∧ pos (par y) < pos y ∧
      (off (lab y) + 1 < pos y → keyOf gen par pos (pts (pos y - 1)) < 16 * pos (par y) + gen y) ∧
      ∀ k, gOK k = true → 16 * pos (par y) + gen y ≤ 16 * pos (T k y) + k)

theorem bfsAt_spec {T : Nat → Nat → Nat} {rt off lab gen par pos pts : Nat → Nat} {y : Nat}
    (h : bfsAt T rt off lab gen par pos pts y = true) : BfsFacts T rt off lab gen par pos pts y := by
  unfold bfsAt at h
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq, strictB_eq] at h
  obtain ⟨h0, h⟩ := h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, by simpa [Nat.blt_eq] using h2,
    Nat.le_of_ble_eq_true h3, by simpa [Nat.blt_eq] using h4, ?_, ?_, ?_⟩
  · intro k hk
    rw [bIf_eq] at h5
    split_ifs at h5 with hr
    · simp only [bAnd_eq, Bool.and_eq_true] at h5
      exact (nbrsOK_spec h5.2.2.2 hk).1
    · unfold inner at h5
      simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h5
      exact (nbrsOK_spec h5.2.2.2.2.2.2 hk).1
  · intro hp
    rw [bIf_eq, if_pos (by rw [hp]; exact Nat.beq_refl _)] at h5
    simp only [bAnd_eq, Bool.and_eq_true] at h5
    exact ⟨Nat.eq_of_beq_eq_true h5.1, Nat.eq_of_beq_eq_true h5.2.1,
      Nat.eq_of_beq_eq_true h5.2.2.1⟩
  · intro hp
    have hb : Nat.beq (pos y) (off (lab y)) = false := by
      cases e : Nat.beq (pos y) (off (lab y))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hp
    rw [bIf_eq, hb, if_neg Bool.false_ne_true] at h5
    unfold inner at h5
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h5
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h5
    refine ⟨g1, by simpa [Nat.blt_eq] using g2, Nat.eq_of_beq_eq_true g3,
      Nat.eq_of_beq_eq_true g4, by simpa [Nat.blt_eq] using g5, fun hlt => ?_,
      fun k hk => (nbrsOK_spec g7 hk).2⟩
    rw [bIf_eq, if_pos (by simpa [Nat.blt_eq] using hlt)] at g6
    simpa [Nat.blt_eq] using g6

theorem depAt_spec {rt lab par dep : Nat → Nat} {y : Nat} (h : depAt rt lab par dep y = true) :
    dep y < 100 ∧ (y = rt (lab y) → dep y = 0) ∧ (y ≠ rt (lab y) → dep y = dep (par y) + 1) := by
  unfold depAt at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, fun hy => ?_, fun hy => ?_⟩
  · rw [if_pos (by rw [← hy]; exact Nat.beq_refl _)] at h2
    exact Nat.eq_of_beq_eq_true h2
  · have hb : Nat.beq y (rt (lab y)) = false := by
      cases e : Nat.beq y (rt (lab y))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hy
    rw [hb, if_neg Bool.false_ne_true] at h2
    exact Nat.eq_of_beq_eq_true h2

theorem bfsHd_spec {rt off lab pos : Nat → Nat} (h : bfsHd rt off lab pos = true) :
    off 0 = 0 ∧ 0 < off 1 ∧ off 1 < off 2 ∧ off 2 < off 3 ∧ off 3 = 31671 ∧
      ∀ c < 3, rt c < 31671 ∧ lab (rt c) = c ∧ pos (rt c) = off c := by
  unfold bfsHd at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, by simpa [Nat.blt_eq] using h2, by simpa [Nat.blt_eq] using h3,
    by simpa [Nat.blt_eq] using h4, Nat.eq_of_beq_eq_true h5, fun c hc => ?_⟩
  have h := allN_iff.1 h6 c hc
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨by simpa [Nat.blt_eq] using h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

end CFSG.KC.Fi23P

end
