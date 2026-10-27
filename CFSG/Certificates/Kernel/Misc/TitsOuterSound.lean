module

public import Certificates.Data.Kernel.Misc.TitsOuter
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.TitsOuter

open CFSG.KC.Enum CFSG.KS

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem labOK_sound {n F : Nat} {A B : List Nat} (h : labOK n F A B = true) :
    ∀ p < n, p ≠ 0 → ∃ q < n, q ≠ p ∧ labAt F q = labAt F p := by
  intro p hp hp0
  have h1 := allN_spec h p hp
  have e : Nat.beq p 0 = false := by
    cases hb : Nat.beq p 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hp0
  rw [e] at h1
  dsimp only at h1
  rw [strictB_eq'] at h1
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
  refine ⟨partK F A B p, Nat.blt_eq.mp h2, fun hq => ?_, Nat.eq_of_beq_eq_true h5⟩
  rw [hq, Nat.beq_refl] at h4
  exact absurd h4 Bool.false_ne_true

end CFSG.KC.TitsOuter

end
