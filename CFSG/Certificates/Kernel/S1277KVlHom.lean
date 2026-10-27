module

public import CFSG.Certificates.Kernel.S1277KSvSound
public import Certificates.Data.Kernel.S1277KVl

public section

namespace CFSG.KS.S1277Vl

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Gm CFSG.KC.S1277Sv
  CFSG.KC.S1277Vl CFSG.KC.Enum CFSG.KS.S1277Lat CFSG.KS.S1277Mod CFSG.KS.S1277Sig CFSG.KS.S1277Gm
  CFSG.KS.S1277Sv CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Surv Certificates.Data.S1277Sig

theorem mul_val_add (w : ℕ) (a b : ZMod 2) : w * (a + b).val = w * a.val ^^^ w * b.val := by
  rw [ZMod.val_add]
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  generalize a.val = x at ha ⊢
  generalize b.val = y at hb ⊢
  interval_cases x <;> interval_cases y <;> simp [Nat.xor_self]

variable {φ : ℕ → ℕ} {u : List ℕ}

section Hom

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}

theorem det_one_of_mul {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : A * B = 1) : A.det = 1 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ _ h2

end Hom

end CFSG.KS.S1277Vl

end
