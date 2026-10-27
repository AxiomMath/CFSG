module

public import Certificates.Data.Kernel.S1277K589102
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (andB orB notB)

theorem inK_iff {N : Nat} {A : Nat → Nat} {x : Nat} :
    inK N A x = true ↔ ∃ i < N, A i = x := by
  unfold inK notInK
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.L34KSnd.notB_iff]
  constructor
  · intro h
    by_contra hne
    have hall : allN N (fun i => CFSG.KLie.CT.notB (Nat.beq (A i) x)) = true :=
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => by
        rw [CFSG.KC.L34KSnd.notB_iff]
        cases e : Nat.beq (A i) x
        · rfl
        · exact absurd ⟨i, hi, Nat.eq_of_beq_eq_true e⟩ hne
    rw [h] at hall
    exact Bool.false_ne_true hall
  · rintro ⟨i, hi, rfl⟩
    cases e : allN N (fun j => CFSG.KLie.CT.notB (Nat.beq (A j) (A i)))
    · rfl
    · have := CFSG.KC.L34KSnd.notB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 e i hi)
      rw [Nat.beq_refl] at this
      exact absurd this (by decide)

theorem clsK_sound {n w m N : Nat} {C A B : Nat → Nat} (h : clsK n w m C N A B = true) :
    (∀ i < m, pcomp n w (mask w) (C i) (C i) = pidn n w → C i ≠ pidn n w →
      (∃ a < N, A a = C i) ∨ ∃ b < N, B b = C i) ∧
    ∀ a < N, ∀ b < N, (¬ ∃ b' < N, B b' = A a) → (¬ ∃ a' < N, A a' = B b) →
      pcomp n w (mask w) (A a) (B b) ≠ pcomp n w (mask w) (B b) (A a) := by
  unfold clsK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  refine ⟨fun i hi hsq hne => ?_, fun a ha b hb hA hB e => ?_⟩
  · rcases CFSG.KC.L34KSnd.orB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h1 i hi) with h3 | h3
    · rw [CFSG.KC.L34KSnd.notB_iff, hsq, Nat.beq_refl] at h3
      exact absurd h3 (by decide)
    rcases CFSG.KC.L34KSnd.orB_iff.1 h3 with h4 | h4
    · exact absurd (Nat.eq_of_beq_eq_true h4) hne
    rcases CFSG.KC.L34KSnd.orB_iff.1 h4 with h5 | h5
    · exact Or.inl (inK_iff.1 h5)
    · exact Or.inr (inK_iff.1 h5)
  · rcases CFSG.KC.L34KSnd.orB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h2 a ha) with h3 | h3
    · exact hA (inK_iff.1 h3)
    rcases CFSG.KC.L34KSnd.orB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 b hb) with h4 | h4
    · exact hB (inK_iff.1 h4)
    · rw [CFSG.KC.L34KSnd.notB_iff, e, Nat.beq_refl] at h4
      exact absurd h4 (by decide)

end CFSG.KC.L34K

end
