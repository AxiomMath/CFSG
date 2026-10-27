module

public import Certificates.Data.Kernel.L34Pow
public import CFSG.Certificates.Kernel.L34Scan2Sound

public section

namespace CFSG.KC.L34Pow

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34KSnd CFSG.KC.L34W
open CFSG.KC.L34Scan2

theorem ppowK_cn {x : Nat} (hx : Cn x) : ∀ k, Cn (ppowK x k)
  | 0 => cn_pidn
  | k + 1 => by
    rw [ppowK_succ]
    exact canonK_pcomp (ppowK_cn hx k) hx

theorem pcomp_pidn {p : Nat} (hp : Cn p) : pcomp 42 6 (mask 6) p (pidn 42 6) = p :=
  eq_of_pg (canonK_pcomp hp cn_pidn) hp fun i hi => by
    rw [pg_pcomp' hp hi, pg_pidn' (by decide) hi]

theorem ppowK_add {x : Nat} (hx : Cn x) (a : Nat) : ∀ b,
    ppowK x (a + b) = pcomp 42 6 (mask 6) (ppowK x a) (ppowK x b)
  | 0 => (pcomp_pidn (ppowK_cn hx a)).symm
  | b + 1 => by
    rw [← Nat.add_assoc, ppowK_succ, ppowK_add hx a b, ppowK_succ,
      pcomp_assoc' (ppowK_cn hx a) (ppowK_cn hx b) hx]

theorem ppowK_mul {x : Nat} (hx : Cn x) (a : Nat) : ∀ b, ppowK x (a * b) = ppowK (ppowK x a) b
  | 0 => rfl
  | b + 1 => by
    rw [Nat.mul_succ, ppowK_add hx, ppowK_mul hx a b, ppowK_succ]

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem with945_eq {x : Nat} (hx : Cn x) (k : Nat → Bool) : with945 x k = k (ppowK x 945) := by
  have e : ppowK (ppowK (ppowK (ppowK (ppowK x 3) 3) 3) 5) 7 = ppowK x (3 * 3 * 3 * 5 * 7) := by
    rw [← ppowK_mul hx 3 3, ← ppowK_mul hx (3 * 3) 3, ← ppowK_mul hx (3 * 3 * 3) 5,
      ← ppowK_mul hx (3 * 3 * 3 * 5) 7]
  unfold with945
  simp only [strictB_app']
  rw [e, (by norm_num : (3 * 3 * 3 * 5 * 7 : Nat) = 945)]

theorem with944_eq {x : Nat} (hx : Cn x) (k : Nat → Bool) : with944 x k = k (ppowK x 944) := by
  have e : ppowK (ppowK (ppowK (ppowK (ppowK x 2) 2) 2) 2) 59 = ppowK x (2 * 2 * 2 * 2 * 59) := by
    rw [← ppowK_mul hx 2 2, ← ppowK_mul hx (2 * 2) 2, ← ppowK_mul hx (2 * 2 * 2) 2,
      ← ppowK_mul hx (2 * 2 * 2 * 2) 59]
  unfold with944
  simp only [strictB_app']
  rw [e, (by norm_num : (2 * 2 * 2 * 2 * 59 : Nat) = 944)]

end CFSG.KC.L34Pow

end
