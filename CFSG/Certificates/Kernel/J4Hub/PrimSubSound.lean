module

public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord

private theorem rec_and_all (f : Nat → Bool) (m : Nat)
    (h : Nat.rec (motive := fun _ => Bool) true (fun mask acc => andB acc (f mask)) m = true) :
    ∀ mask < m, f mask = true := by
  induction m with
  | zero => intro mask hm; omega
  | succ m ih =>
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun mask acc => andB acc (f mask)) m)
        (f m) = true := h
    have hl : Nat.rec (motive := fun _ => Bool) true (fun mask acc => andB acc (f mask)) m = true ∧
        f m = true := by
      cases hb : Nat.rec (motive := fun _ => Bool) true (fun mask acc => andB acc (f mask)) m <;>
        simp_all [andB]
    intro mask hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
    · exact ih hl.1 mask hlt
    · exact hl.2

theorem primSub_sound' {sizes n N : Nat} (h : CFSG.KC.Fam.primSub sizes n N = true) :
    ∀ mask < 2 ^ n, mask ≠ 0 → mask ≠ 2 ^ n - 1 → ¬ CFSG.KC.Fam.subSize sizes mask n ∣ N := by
  intro mask hm h0 h1 hd
  have hall := rec_and_all _ _ h mask (by simpa [Nat.shiftLeft_eq] using hm)
  have hmod : N % CFSG.KC.Fam.subSize sizes mask n = 0 := Nat.mod_eq_zero_of_dvd hd
  have e1 : Nat.beq mask 0 = false := by
    cases hb : Nat.beq mask 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h0
  have e2 : Nat.beq mask (Nat.sub (Nat.shiftLeft 1 n) 1) = false := by
    cases hb : Nat.beq mask (Nat.sub (Nat.shiftLeft 1 n) 1)
    · rfl
    · exact absurd (by simpa [Nat.shiftLeft_eq] using Nat.eq_of_beq_eq_true hb) h1
  have e3 : Nat.beq (Nat.mod N (CFSG.KC.Fam.subSize sizes mask n)) 0 = true := by
    show Nat.beq (N % _) 0 = true
    rw [hmod]; rfl
  simp only [e1, e2, e3] at hall
  simp [orB, notB] at hall

end CFSG.KS.J4Hub

end
