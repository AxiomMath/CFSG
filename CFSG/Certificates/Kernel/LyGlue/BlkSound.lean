module

public import Certificates.Data.Kernel.LyGlue.Defs
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.LyGlue

open CFSG.KC.Enum CFSG.KS

theorem bIf_true_iff (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = true ↔ (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem blkOK_spec {deg n ng wH : Nat} {F : Nat → Nat} {gpt : Nat → Nat → Nat} {H : Nat → Nat}
    (h : blkOK deg n ng wH F gpt H = true) :
    ∀ a < deg, F a ≠ 65535 → F a < n ∧ ∀ k < ng, F (gpt k a) = pg wH (mask wH) (H k) (F a) := by
  intro a ha hne
  have h1 := allN_spec h a ha
  rw [CFSG.KS.PF.strictB_eqP] at h1
  rcases (bIf_true_iff _ _ _).1 h1 with ⟨hb, -⟩ | ⟨-, h2⟩
  · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  · obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    refine ⟨Nat.blt_eq.mp h3, fun k hk => ?_⟩
    exact Nat.eq_of_beq_eq_true (allN_spec h4 k hk)

theorem secOK_spec {deg n : Nat} {F S : Nat → Nat} (h : secOK deg n F S = true) :
    ∀ j < n, S j < deg ∧ F (S j) = j := by
  intro j hj
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec h j hj)
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

end CFSG.KC.LyGlue

end
