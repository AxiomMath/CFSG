module

public import Certificates.Data.Kernel.Th3Local.Defs
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel

public section

namespace CFSG.KC.Th3Local

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem ordPk_spec {g : J} {M p : ℕ} (hp : p.Prime) (hp64 : p < 64) (hM : 𝕄 g = pkMat M)
    (h : ordPk c rm ONE M p = true) : orderOf g = p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold ordPk at h
  cases ha : Nat.beq (powB c rm ONE M p 6) ONE
  · rw [ha] at h
    exact absurd h Bool.false_ne_true
  rw [ha] at h
  have h1 : 𝕄 (g ^ p) = 𝕄 (1 : J) := by
    rw [mat_pow, mat_one, hM, ← pkMat_powB hk M p 6 (by omega), Nat.eq_of_beq_eq_true ha,
      pkMat_one hk]
  refine orderOf_eq_prime (mat_injective h1) ?_
  rintro rfl
  have e : mulB c rm M ONE = ONE := by
    refine pkMat_inj (inLayout_mulB hk _ _) (inLayout_one hk) ?_
    rw [pkMat_mulB hk, ← hM, pkMat_one hk, mat_one, Matrix.one_mul]
  rw [e, Nat.beq_refl] at h
  exact absurd h Bool.false_ne_true

theorem commPk_spec {g h : J} {M N : ℕ} (hM : 𝕄 g = pkMat M) (hN : 𝕄 h = pkMat N)
    (e : commPk c rm M N = true) : g * h = h * g := by
  have e' : 𝕄 (g * h) = 𝕄 (h * g) := by
    rw [mat_mul, mat_mul, hM, hN, ← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true e]
  exact mat_injective e'

end CFSG.KC.Th3Local

end
