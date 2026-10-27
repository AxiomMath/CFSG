module

public import Certificates.Data.Kernel.LocalQT.M11
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.KC.LQT.M

open Equiv CFSG.KC.LQT.S

theorem forall_lt_11 {p : ℕ → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) (h4 : p 4)
    (h5 : p 5) (h6 : p 6) (h7 : p 7) (h8 : p 8) (h9 : p 9) (h10 : p 10) : ∀ c < 11, p c := by
  intro c hc
  interval_cases c <;> assumption

theorem cntL_append (a b LF : List ℕ) : cntL (a ++ b) LF = cntL a LF + cntL b LF := by
  induction a with
  | nil => exact (Nat.zero_add _).symm
  | cons x a ih =>
    have e : ∀ l, cntL (x :: l) LF = cntY x LF + cntL l LF := fun _ => rfl
    rw [List.cons_append, e, e, ih, Nat.add_assoc]

theorem tripL_append (a b LI : List ℕ) :
    tripL (a ++ b) LI = CFSG.KC.Ord.andB (tripL a LI) (tripL b LI) := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    have e : ∀ l, tripL (x :: l) LI = CFSG.KC.Ord.andB (rowT x LI) (tripL l LI) := fun _ => rfl
    rw [List.cons_append, e, e, ih]
    cases rowT x LI <;> rfl

theorem cntOK_append {a b LF : List ℕ} {m k : ℕ} (ha : cntOK a LF m = true)
    (hb : cntOK b LF k = true) : cntOK (a ++ b) LF (m + k) = true := by
  unfold cntOK at ha hb ⊢
  rw [cntL_append, Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true hb]
  exact Nat.beq_refl _

theorem tripL_append_true {a b LI : List ℕ} (ha : tripL a LI = true) (hb : tripL b LI = true) :
    tripL (a ++ b) LI = true := by
  rw [tripL_append, ha, hb]
  rfl

end CFSG.KC.LQT.M

end
