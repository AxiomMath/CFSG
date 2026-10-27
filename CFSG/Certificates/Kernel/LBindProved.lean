module

public import Certificates.Data.Kernel.LBind
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem lbindRun_sound {n w P : Nat} :
    ∀ (L : List Nat) (i : Nat), lbindRun n w P L i = true →
      i + L.length = n ∧ ∀ j (hj : j < L.length), L[j] = pg w (mask w) P (i + j) := by
  intro L
  induction L with
  | nil =>
    intro i h
    exact ⟨Nat.eq_of_beq_eq_true h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons a L ih =>
    intro i h
    change Bool.rec (motive := fun _ => Bool) false (lbindRun n w P L (Nat.succ i))
      (Nat.beq a (pg w (mask w) P i)) = true at h
    cases ha : Nat.beq a (pg w (mask w) P i)
    · rw [ha] at h
      exact absurd h Bool.false_ne_true
    · rw [ha] at h
      obtain ⟨h1, h2⟩ := ih (i + 1) h
      refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
      cases j with
      | zero => simpa using Nat.eq_of_beq_eq_true ha
      | succ j =>
        have := h2 j (by simpa using hj)
        simp only [List.getElem_cons_succ]
        rw [this]
        congr 1
        omega

theorem lbindK_sound_proved {L : List Nat} {n w P : Nat} (h : lbindK L n w P = true) :
    L.toArray = unpack n w P := by
  obtain ⟨h1, h2⟩ := lbindRun_sound L 0 h
  rw [Nat.zero_add] at h1
  apply Array.ext
  · simp [unpack, h1]
  · intro j hj1 hj2
    simp only [List.getElem_toArray, unpack, Array.getElem_ofFn]
    rw [h2 j (by simpa using hj1), Nat.zero_add]

end CFSG.KS.Raw

end
