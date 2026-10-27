module

public import Certificates.Data.Kernel.Spor.RawSlP
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem szOK_facts' {n w : Nat} (h : szOK n w = true) : n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have h3 := Nat.blt_eq.mp h2
  have e : Nat.shiftLeft (nat_lit 1) w = 2 ^ w := by
    change 1 <<< w = 2 ^ w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e] at h3
  exact ⟨Nat.blt_eq.mp h1, h3⟩

theorem pg_zero_of_ge {n w q v : Nat} (hq : q >>> (n * w) = 0) (hv : n ≤ v) :
    pg w (mask w) q v = 0 := by
  have e : w * v = n * w + (w * v - n * w) := by
    have : n * w ≤ w * v := by rw [Nat.mul_comm n w]; exact Nat.mul_le_mul_left w hv
    omega
  change (q >>> (w * v)) &&& mask w = 0
  rw [e, Nat.shiftRight_add, hq, Nat.zero_shiftRight, Nat.zero_and]

theorem eq2_of_pcomp {n w r p q : Nat} (hn : n < 2 ^ 32)
    (h : Nat.beq r (pcomp n w (mask w) p q) = true) : eq2 n w (mask w) r p q = true := by
  have e := Nat.eq_of_beq_eq_true h
  unfold eq2
  exact allN_of_forall fun i hi => by
    rw [e, CFSG.KS.PF.pg_pcomp hn hi]
    exact Nat.beq_refl _

theorem permOK_of_invP {n w p q : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (h : invP n w (mask w) (n * w) p q = true) : permOK n w (mask w) (n * w) p q = true := by
  unfold invP at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  have e4 : pcomp n w (mask w) q p = pidn n w := Nat.eq_of_beq_eq_true h4
  have hq0 : q >>> (n * w) = 0 := Nat.eq_of_beq_eq_true h2
  have h32 : n < 2 ^ 32 := Nat.lt_trans hn (by decide)
  have inv : ∀ i < n, pg w (mask w) q (pg w (mask w) p i) = i := by
    intro i hi
    rw [← CFSG.KS.PF.pg_pcomp h32 hi, e4, CFSG.KS.PF.pg_pidn hn hw hi]
  unfold permOK
  refine (bAnd_iff _ _).2 ⟨h1, (bAnd_iff _ _).2 ⟨h2, allN_of_forall fun i hi => ?_⟩⟩
  rw [strictB_eq]
  refine (bAnd_iff _ _).2 ⟨?_, by rw [inv i hi]; exact Nat.beq_refl _⟩
  rcases Nat.eq_zero_or_pos i with i0 | i0
  · subst i0
    exact h3
  · apply Nat.blt_eq.mpr
    rcases Nat.lt_or_ge (pg w (mask w) p i) n with hl | hge
    · exact hl
    · have := inv i hi
      rw [pg_zero_of_ge hq0 hge] at this
      omega

theorem lvKK_of_P {n w kS T R c r o k : Nat} {S SI TR TRI : Nat → Nat} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (h : lvKKP n w (mask w) (n * w) S SI TR TRI kS T R c r o k = true) :
    lvKK n w (mask w) (n * w) S SI TR TRI kS T R c r o k = true := by
  unfold lvKKP at h
  unfold lvKK
  obtain ⟨a1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a5, a6⟩ := (bAnd_iff _ _).1 h
  refine (bAnd_iff _ _).2 ⟨a1, (bAnd_iff _ _).2 ⟨a2, (bAnd_iff _ _).2 ⟨a3, (bAnd_iff _ _).2 ⟨a4,
    (bAnd_iff _ _).2 ⟨?_, permOK_of_invP hn hw a6⟩⟩⟩⟩⟩
  revert a5
  cases Nat.beq k (nat_lit 0)
  · exact eq2_of_pcomp (Nat.lt_trans hn (by decide))
  · exact fun _ => rfl

theorem lvPtK_of_P {n w kS T R c r o k : Nat} {S SI TR TRI : Nat → Nat} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (h : lvPtKP n w (mask w) (n * w) S SI TR TRI kS T R c r o k = true) :
    lvPtK n w (mask w) (n * w) S SI TR TRI kS T R c r o k = true := by
  unfold lvPtKP at h
  unfold lvPtK
  obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 h
  refine (bAnd_iff _ _).2 ⟨b1, ?_⟩
  revert b2
  cases Nat.blt k c
  · exact id
  · exact lvKK_of_P hn hw

theorem lvSlK_of_P (n w : Nat) (S SI TR TRI : Nat → Nat) (kS T R lo len : Nat)
    (hsz : szOK n w = true) (h : lvSlKP n w (mask w) (n * w) S SI TR TRI kS T R lo len = true) :
    lvSlK n w (mask w) (n * w) S SI TR TRI kS T R lo len = true := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  unfold lvSlKP at h
  unfold lvSlK
  exact allN_of_forall fun d hd => lvPtK_of_P hn hw (allN_spec h d hd)

end CFSG.KS.Raw

end
