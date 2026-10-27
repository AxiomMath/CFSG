
module

public import CFSG.Certificates.Kernel.ThDemp.OrbU
public import CFSG.Certificates.Kernel.ThDemp.OrbitCount
public import CFSG.Certificates.Kernel.ThDemp.Sound
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace CFSG.Certificates.ThDemp.Cent

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.OrbitCount

set_option exponentiation.threshold 2000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

@[ext] structure Vec where
  v : Fin 248 → ZMod 2

instance : MulAction (GL (Fin 248) (ZMod 2)) Vec where
  smul g w := ⟨Matrix.vecMul w.v ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))⟩
  one_smul w := by
    ext1
    change Matrix.vecMul w.v ((1⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = w.v
    rw [inv_one, Units.val_one, Matrix.vecMul_one]
  mul_smul g h w := by
    ext1
    change Matrix.vecMul w.v (((g * h)⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
      Matrix.vecMul (Matrix.vecMul w.v ((h⁻¹ : GL (Fin 248) (ZMod 2)) :
        Matrix (Fin 248) (Fin 248) (ZMod 2))) ((g⁻¹ : GL (Fin 248) (ZMod 2)) :
        Matrix (Fin 248) (Fin 248) (ZMod 2))
    rw [mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul]

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

theorem smul_vec_gl (g : GL (Fin 248) (ZMod 2)) (w : Vec) :
    (g • w).v = Matrix.vecMul w.v ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) :=
  rfl

theorem smul_vec (g : J) (w : Vec) : (g • w).v = Matrix.vecMul w.v (𝕄 g⁻¹) := by
  rw [Subgroup.smul_def, smul_vec_gl, Subgroup.coe_inv]

@[expose] noncomputable def fixSub (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) :
    Submodule (ZMod 2) (Fin 248 → ZMod 2) where
  carrier := {w | Matrix.vecMul w M = w}
  add_mem' {a b} ha hb := by
    change Matrix.vecMul (a + b) M = a + b
    rw [Matrix.add_vecMul, ha, hb]
  zero_mem' := Matrix.zero_vecMul M
  smul_mem' c w hw := by
    change Matrix.vecMul (c • w) M = c • w
    rw [Matrix.smul_vecMul, hw]

theorem mem_fixSub {M : Matrix (Fin 248) (Fin 248) (ZMod 2)} {w : Fin 248 → ZMod 2} :
    w ∈ fixSub M ↔ Matrix.vecMul w M = w := Iff.rfl

theorem rowsOf_five {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 2 ^ 248) (h1 : a1 < 2 ^ 248)
    (h2 : a2 < 2 ^ 248) (h3 : a3 < 2 ^ 248) (h4 : a4 < 2 ^ 248) :
    rowsOf (2 ^ 248 - 1) (Nat.lor (Nat.lor (Nat.lor (Nat.lor a0 (Nat.shiftLeft a1 256))
      (Nat.shiftLeft a2 512)) (Nat.shiftLeft a3 768)) (Nat.shiftLeft a4 1024)) =
      [a0, a1, a2, a3, a4] := by
  set F : ℕ → ℕ := fun k => [a0, a1, a2, a3, a4].getD k 0
  have hF : ∀ k < 5, F k < 2 ^ 248 := by
    intro k hk
    interval_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have e : Nat.lor (Nat.lor (Nat.lor (Nat.lor a0 (Nat.shiftLeft a1 256))
      (Nat.shiftLeft a2 512)) (Nat.shiftLeft a3 768)) (Nat.shiftLeft a4 1024) = stackN 256 5 F := by
    rw [stackN_succ, stackN_succ, stackN_succ, stackN_succ, stackN_succ]
    change _ = 0 ||| a0 <<< (256 * 0) ||| a1 <<< (256 * 1) ||| a2 <<< (256 * 2) |||
      a3 <<< (256 * 3) ||| a4 <<< (256 * 4)
    rw [Nat.zero_or, Nat.mul_zero, Nat.shiftLeft_zero]
    rfl
  rw [e]
  have r := fun k (hk : k < 5) => row_stackN hF hk
  have r0 : Nat.land (stackN 256 5 F) (2 ^ 248 - 1) = a0 := by
    have := r 0 (by omega)
    simp only [Nat.mul_zero, Nat.shiftRight_zero] at this
    exact this
  have r1 : Nat.land (Nat.shiftRight (stackN 256 5 F) 256) (2 ^ 248 - 1) = a1 := r 1 (by omega)
  have r2 : Nat.land (Nat.shiftRight (stackN 256 5 F) 512) (2 ^ 248 - 1) = a2 := r 2 (by omega)
  have r3 : Nat.land (Nat.shiftRight (stackN 256 5 F) 768) (2 ^ 248 - 1) = a3 := r 3 (by omega)
  have r4 : Nat.land (Nat.shiftRight (stackN 256 5 F) 1024) (2 ^ 248 - 1) = a4 := r 4 (by omega)
  change [Nat.land (stackN 256 5 F) _, Nat.land (Nat.shiftRight (stackN 256 5 F) 256) _,
    Nat.land (Nat.shiftRight (stackN 256 5 F) 512) _, Nat.land (Nat.shiftRight (stackN 256 5 F) 768) _,
    Nat.land (Nat.shiftRight (stackN 256 5 F) 1024) _] = _
  rw [r0, r1, r2, r3, r4]

structure CentFacts (D : DempData) (O : OrbData) : Prop where
  c5 : cent5 D (chainEl D O.x5) ≤ 2
  c31 : cent5 D (chainEl D O.x31) ≤ 1
  fixRows : eqRows D (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) (uAll D) ≤ 2
  kerRows : eqRows D (uAll D ^^^ mulB (cR 32) D.rm (uAll D) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5))
      (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D)
      (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) 0 ≤ 16
  f5 : O.f5 < 32
  f5row : rowAt D (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) O.f5 = rowAt D (uAll D) O.f5
  v5 : O.v5 < 32
  v5row : rowAt D (uAll D ^^^ mulB (cR 32) D.rm (uAll D) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5))
      (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D)
      (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) O.v5 = 0
  gs5 : combChk D.rm (U0 D) (cycPt D (chainEl D O.x5) (uVec D O.v5) (uVec D O.f5)) O.gs5 = true
  gs31 : combChk D.rm (U0 D) (cycPt D (chainEl D O.x31) (D.bvL 0) (vecB D.rm (vecB D.rm (vecB D.rm
    (vecB D.rm (D.bvL 0) (chainEl D O.x31)) (chainEl D O.x31)) (chainEl D O.x31)) (chainEl D O.x31)))
    O.gs31 = true

theorem centChk_facts (h : centChk D O = true) : CentFacts D O := by
  unfold centChk at h
  simp only [strictB_eq] at h
  obtain ⟨c5, h⟩ := Unfold.andB_split h
  obtain ⟨c31, h⟩ := Unfold.andB_split h
  obtain ⟨e1, h⟩ := Unfold.andB_split h
  obtain ⟨e2, h⟩ := Unfold.andB_split h
  obtain ⟨-, h⟩ := Unfold.andB_split h
  obtain ⟨f5, h⟩ := Unfold.andB_split h
  obtain ⟨f5r, h⟩ := Unfold.andB_split h
  obtain ⟨-, h⟩ := Unfold.andB_split h
  obtain ⟨v5, h⟩ := Unfold.andB_split h
  obtain ⟨v5r, h⟩ := Unfold.andB_split h
  obtain ⟨g5, g31⟩ := Unfold.andB_split h
  exact ⟨Nat.ble_eq.mp c5, Nat.ble_eq.mp c31, Nat.ble_eq.mp e1, Nat.ble_eq.mp e2, Nat.blt_eq.mp f5,
    Nat.eq_of_beq_eq_true f5r, Nat.blt_eq.mp v5, Nat.eq_of_beq_eq_true v5r, g5, g31⟩

theorem inv_comm_of_mem_cent {G : Type*} [Group G] {x c : G}
    (h : c ∈ Subgroup.centralizer ({x} : Set G)) : c⁻¹ * x = x * c⁻¹ := by
  have h1 : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp h
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]

namespace Ctx

variable (hF : DempFacts D)
include hF

theorem cent5_eq (X : ℕ) : cent5 D X = ((Finset.range 32).filter
    (fun y => D.mul (D.T 5 y) X = D.mul X (D.T 5 y))).card := by
  unfold cent5
  rw [Unfold.card_filter_of_sumBelow (by norm_num)]
  congr 1

@[expose] noncomputable def nrm (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) (w : Fin 248 → ZMod 2) :
    Fin 248 → ZMod 2 :=
  w + Matrix.vecMul w M + Matrix.vecMul (Matrix.vecMul w M) M +
    Matrix.vecMul (Matrix.vecMul (Matrix.vecMul w M) M) M +
    Matrix.vecMul (Matrix.vecMul (Matrix.vecMul (Matrix.vecMul w M) M) M) M

omit hF in
theorem nrm_mul (M N : Matrix (Fin 248) (Fin 248) (ZMod 2)) (hMN : M * N = N * M)
    (w : Fin 248 → ZMod 2) : nrm M (Matrix.vecMul w N) = Matrix.vecMul (nrm M w) N := by
  have h : ∀ u : Fin 248 → ZMod 2, Matrix.vecMul (Matrix.vecMul u N) M =
      Matrix.vecMul (Matrix.vecMul u M) N := fun u => by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hMN]
  simp only [nrm, Matrix.add_vecMul, h]

theorem fix_vecB {X v : ℕ} {G : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hG : pkMat X * G = G * pkMat X)
    (hv : Matrix.vecMul (pkVec v) G = pkVec v) :
    Matrix.vecMul (pkVec (vecB D.rm v X)) G = pkVec (vecB D.rm v X) := by
  rw [pkVec_vecB hF.consts, Matrix.vecMul_vecMul, hG, ← Matrix.vecMul_vecMul, hv]

end Ctx

end CFSG.Certificates.ThDemp.Cent

end
