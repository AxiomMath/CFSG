module

public import Certificates.Data.Kernel.PermCent.SmallB
public import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Sporadic.Schreier

variable {n : Nat} [Small n]

theorem cOf_one : cOf (1 : Equiv.Perm (Fin n)) = 1 :=
  ev_injective (by rw [ev_cOf, ev_one])

theorem ev_evCodesB (S : List (Equiv.Perm (Fin n))) (w : List ℤ) :
    ev (evCodesB (S.map cOf) w) = evalCodes S w := by
  induction w with
  | nil => rw [evCodesB, evalCodes, ev_one]
  | cons z w ih =>
    rw [evCodesB, evalCodes, ev_mul, ih, ← cOf_one, List.getD_map, List.getD_map]
    split
    · rw [ev_cOf]
    · rw [ev_inv, ev_cOf]

theorem cOf_evalCodes (S : List (Equiv.Perm (Fin n))) (w : List ℤ) :
    cOf (evalCodes S w) = evCodesB (S.map cOf) w :=
  ev_injective (by rw [ev_cOf, ev_evCodesB])

theorem orderIs_eq_P {M : Type*} [Monoid M] [DecidableEq M] (g : M) (m : Nat) (ps : List Nat)
    (hm : 0 < m) (h1 : ∀ p < m + 1, p.Prime → p ∣ m → p ∈ ps)
    (h2 : ∀ p ∈ ps, p.Prime ∧ p ∣ m) : orderIs g m = orderIsP g m ps :=
  orderIs_eq_orderIsP g hm ps (fun p hp hd => h1 p (Nat.lt_succ_of_le (Nat.le_of_dvd hm hd)) hp hd) h2

end CFSG.Certificates.Kernel.PkCV

end
