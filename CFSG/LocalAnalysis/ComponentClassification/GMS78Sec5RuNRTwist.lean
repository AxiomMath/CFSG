module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRModel
public import Certificates.Data.GMS78RuSModelData

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode

local instance : Std.Associative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

local instance : Std.Commutative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

@[ext] structure X8 where
  v : Fin 8

namespace X8

instance : Zero X8 := ⟨⟨0⟩⟩

instance : Add X8 := ⟨fun a b => ⟨a.v ^^^ b.v⟩⟩

instance : Neg X8 := ⟨fun a => a⟩

instance : AddCommGroup X8 where
  add_assoc a b c := X8.ext (by change (a.v ^^^ b.v) ^^^ c.v = a.v ^^^ (b.v ^^^ c.v); ac_rfl)
  zero_add a := X8.ext (fin8_zero_xor a.v)
  add_zero a := X8.ext (fin8_xor_zero a.v)
  add_comm a b := X8.ext (by change a.v ^^^ b.v = b.v ^^^ a.v; ac_rfl)
  neg_add_cancel a := X8.ext (fin8_xor_self a.v)
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem v_add (a b : X8) : (a + b).v = a.v ^^^ b.v := rfl

theorem v_zero : (0 : X8).v = 0 := rfl

theorem add_self (a : X8) : a + a = 0 := X8.ext (fin8_xor_self a.v)

end X8

theorem fadd_self (F : Fin 256 → X8) : F + F = 0 := funext fun i => X8.add_self (F i)

theorem odd_nsmul_eq (F : Fin 256 → X8) (n : ℕ) : (2 * n + 1) • F = F := by
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, fadd_self, nsmul_zero, zero_add]

theorem fin8_eq_of_xor_eq_zero {a b : Fin 8} (h : a ^^^ b = 0) : a = b := by
  revert h
  revert a b
  decide

@[expose] def linExt (lam : ℕ → Fin 8) (m : ℕ) : Fin 8 := xs8 (nCo m) lam

theorem linExt_xor (lam : ℕ → Fin 8) (m n : ℕ) :
    linExt lam (m ^^^ n) = linExt lam m ^^^ linExt lam n := by
  simp only [linExt, nCo_xor, xs8_xor]

@[expose] def shear (F : Fin 256 → Fin 8) (x : RuR) : RuR := ⟨x.m, x.t ^^^ F x.m⟩

theorem fin256_xor_zero (a : Fin 256) : a ^^^ 0 = a := by
  apply Fin.ext
  rw [fin256_val_xor]
  exact Nat.xor_zero _

theorem fin256_zero_xor (a : Fin 256) : 0 ^^^ a = a := by
  apply Fin.ext
  rw [fin256_val_xor]
  exact Nat.zero_xor _

theorem mul_A1 (x : RuR) (a : Fin 8) : x * ⟨0, a⟩ = ⟨x.m, x.t ^^^ a⟩ := by
  rw [RuR.mul_def]
  refine RuR.ext (fin256_xor_zero _) ?_
  change x.t ^^^ a ^^^ nBeta x.m.val 0 = x.t ^^^ a
  rw [nBeta_zero_right, fin8_xor_zero]

theorem eq_mk_mul (x : RuR) : x = ⟨x.m, 0⟩ * ⟨0, x.t⟩ := by
  rw [mul_A1, fin8_zero_xor]

theorem shear_eq_mul (F : Fin 256 → Fin 8) (x : RuR) : shear F x = x * ⟨0, F x.m⟩ := by
  rw [mul_A1]
  rfl

theorem shear_shear (F G : Fin 256 → Fin 8) (x : RuR) :
    shear F (shear G x) = shear (fun n => G n ^^^ F n) x := by
  refine RuR.ext rfl ?_
  change x.t ^^^ G x.m ^^^ F x.m = x.t ^^^ (G x.m ^^^ F x.m)
  ac_rfl

theorem fin8_xor_xor_self (a b : Fin 8) : a ^^^ b ^^^ b = a := by
  revert a b
  decide

@[expose] def cAut (lam : ℕ → Fin 8) : MulAut RuR where
  toFun x := ⟨x.m, x.t ^^^ linExt lam x.m.val⟩
  invFun x := ⟨x.m, x.t ^^^ linExt lam x.m.val⟩
  left_inv x := by
    refine RuR.ext rfl ?_
    change x.t ^^^ linExt lam x.m.val ^^^ linExt lam x.m.val = x.t
    exact fin8_xor_xor_self _ _
  right_inv x := by
    refine RuR.ext rfl ?_
    change x.t ^^^ linExt lam x.m.val ^^^ linExt lam x.m.val = x.t
    exact fin8_xor_xor_self _ _
  map_mul' x y := by
    refine RuR.ext rfl ?_
    change (x * y).t ^^^ linExt lam (x * y).m.val =
      (x.t ^^^ linExt lam x.m.val) ^^^ (y.t ^^^ linExt lam y.m.val) ^^^ nBeta x.m.val y.m.val
    rw [RuR.mul_def]
    change x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val ^^^ linExt lam (x.m ^^^ y.m).val = _
    rw [fin256_val_xor, linExt_xor]
    ac_rfl

theorem cAut_apply (lam : ℕ → Fin 8) (x : RuR) :
    cAut lam x = ⟨x.m, x.t ^^^ linExt lam x.m.val⟩ := rfl

theorem cAut_mul_self (lam : ℕ → Fin 8) : cAut lam * cAut lam = 1 :=
  MulEquiv.ext fun _ => RuR.ext rfl (fin8_xor_xor_self _ _)

theorem cAut_m (lam : ℕ → Fin 8) (x : RuR) : (cAut lam x).m = x.m := rfl

theorem cAut_A1 (lam : ℕ → Fin 8) (t : Fin 8) : cAut lam ⟨0, t⟩ = ⟨0, t⟩ := by
  refine RuR.ext rfl ?_
  change t ^^^ xs8 (nCo 0) lam = t
  rw [nCo_zero, xs8_zero, fin8_xor_zero]

@[expose] def shearX (F : Fin 256 → X8) (x : RuR) : RuR := shear (fun n => (F n).v) x

theorem shearX_shearX (F G : Fin 256 → X8) (x : RuR) :
    shearX F (shearX G x) = shearX (G + F) x :=
  shear_shear _ _ x

theorem shearX_zero (x : RuR) : shearX 0 x = x := RuR.ext rfl (fin8_xor_zero x.t)

theorem shearX_ext {F G : Fin 256 → X8} (h : ∀ x, shearX F x = shearX G x) : F = G := by
  funext n
  have e := congrArg RuR.t (h ⟨n, 0⟩)
  change (0 : Fin 8) ^^^ (F n).v = (0 : Fin 8) ^^^ (G n).v at e
  rw [fin8_zero_xor, fin8_zero_xor] at e
  exact X8.ext e

@[expose] def shearOf (φ : MulAut RuR) (n : Fin 256) : Fin 8 := (φ ⟨n, 0⟩).t

theorem apply_eq_shear {φ : MulAut RuR} (hm : ∀ x, (φ x).m = x.m)
    (hA : ∀ t, φ ⟨0, t⟩ = ⟨0, t⟩) (x : RuR) : φ x = shear (shearOf φ) x := by
  conv_lhs => rw [eq_mk_mul x]
  rw [map_mul, hA, mul_A1]
  refine RuR.ext (hm _) ?_
  change (φ ⟨x.m, 0⟩).t ^^^ x.t = x.t ^^^ (φ ⟨x.m, 0⟩).t
  ac_rfl

theorem fin8_xor_cancel_left (a b c : Fin 8) (h : a ^^^ b = c ^^^ a) : b = c := by
  revert h
  revert a b c
  decide

theorem shearOf_xor {φ : MulAut RuR} (hm : ∀ x, (φ x).m = x.m) (hA : ∀ t, φ ⟨0, t⟩ = ⟨0, t⟩)
    (n n' : Fin 256) : shearOf φ (n ^^^ n') = shearOf φ n ^^^ shearOf φ n' := by
  have h1 : (⟨n, 0⟩ : RuR) * ⟨n', 0⟩ = ⟨n ^^^ n', nBeta n.val n'.val⟩ := by
    rw [RuR.mul_def]
    refine RuR.ext rfl ?_
    change (0 : Fin 8) ^^^ 0 ^^^ nBeta n.val n'.val = nBeta n.val n'.val
    rw [fin8_xor_zero, fin8_zero_xor]
  have h2 := congrArg RuR.t (map_mul φ (⟨n, 0⟩ : RuR) ⟨n', 0⟩)
  rw [h1, apply_eq_shear hm hA, apply_eq_shear hm hA ⟨n, 0⟩,
    apply_eq_shear hm hA ⟨n', 0⟩, RuR.mul_def] at h2
  change nBeta n.val n'.val ^^^ shearOf φ (n ^^^ n') =
    (0 ^^^ shearOf φ n) ^^^ (0 ^^^ shearOf φ n') ^^^ nBeta n.val n'.val at h2
  rw [fin8_zero_xor, fin8_zero_xor] at h2
  exact fin8_xor_cancel_left _ _ _ h2

@[expose] def innerS (m : Fin 256) : Fin 256 → X8 :=
  fun n => ⟨nBeta m.val n.val ^^^ nBeta n.val m.val⟩

theorem conj_eq_shearX (z x : RuR) : MulAut.conj z x = shearX (innerS z.m) x := by
  rw [MulAut.conj_apply]
  refine RuR.ext ?_ ?_
  · change (z.m ^^^ x.m) ^^^ z.m = x.m
    apply Fin.ext
    rw [fin256_val_xor, fin256_val_xor, Nat.xor_comm z.m.val, Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  · change (z.t ^^^ x.t ^^^ nBeta z.m.val x.m.val) ^^^ (z.t ^^^ nBeta z.m.val z.m.val) ^^^
      nBeta (z.m ^^^ x.m).val z.m.val = x.t ^^^ (nBeta z.m.val x.m.val ^^^ nBeta x.m.val z.m.val)
    rw [fin256_val_xor, nBeta_xor_left]
    calc _ = x.t ^^^ (nBeta z.m.val x.m.val ^^^ nBeta x.m.val z.m.val) ^^^ (z.t ^^^ z.t) ^^^
          (nBeta z.m.val z.m.val ^^^ nBeta z.m.val z.m.val) := by ac_rfl
      _ = _ := by rw [fin8_xor_self, fin8_xor_self, fin8_xor_zero, fin8_xor_zero]

theorem innerS_xor (m m' : Fin 256) : innerS (m ^^^ m') = innerS m + innerS m' := by
  funext n
  refine X8.ext ?_
  change nBeta (m ^^^ m').val n.val ^^^ nBeta n.val (m ^^^ m').val =
    (nBeta m.val n.val ^^^ nBeta n.val m.val) ^^^ (nBeta m'.val n.val ^^^ nBeta n.val m'.val)
  rw [fin256_val_xor, nBeta_xor_left, nBeta_xor_right]
  ac_rfl

theorem innerS_apply_xor (m n n' : Fin 256) :
    innerS m (n ^^^ n') = innerS m n + innerS m n' := by
  refine X8.ext ?_
  change nBeta m.val (n ^^^ n').val ^^^ nBeta (n ^^^ n').val m.val =
    (nBeta m.val n.val ^^^ nBeta n.val m.val) ^^^ (nBeta m.val n'.val ^^^ nBeta n'.val m.val)
  rw [fin256_val_xor, nBeta_xor_left, nBeta_xor_right]
  ac_rfl

theorem innerS_zero : innerS 0 = 0 := by
  funext n
  refine X8.ext ?_
  change nBeta 0 n.val ^^^ nBeta n.val 0 = 0
  rw [nBeta_zero_left, nBeta_zero_right, fin8_xor_zero]

@[expose] def innerI : AddSubgroup (Fin 256 → X8) where
  carrier := {F | ∃ m, F = innerS m}
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m ^^^ m', (innerS_xor m m').symm⟩
  zero_mem' := ⟨0, innerS_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, rfl⟩

theorem mem_innerI_iff (F : Fin 256 → X8) : F ∈ innerI ↔ ∃ m, F = innerS m := Iff.rfl

theorem innerS_mem (m : Fin 256) : innerS m ∈ innerI := ⟨m, rfl⟩

theorem mem_innerI_of_shearX {M : Subgroup (MulAut RuR)}
    (hker : ∀ f ∈ M, (∀ x, (f x).m = x.m) → (∀ t, f ⟨0, t⟩ = ⟨0, t⟩) →
      ∃ y, f = MulAut.conj y)
    {e : MulAut RuR} (he : e ∈ M) {F : Fin 256 → X8} (hF : ∀ x, e x = shearX F x) :
    F ∈ innerI := by
  have h0 : (F 0).v = 0 := by
    have h1 := congrArg RuR.t (hF 1)
    rw [map_one] at h1
    change (0 : Fin 8) = (0 : Fin 8) ^^^ (F 0).v at h1
    rw [fin8_zero_xor] at h1
    exact h1.symm
  obtain ⟨y, rfl⟩ := hker e he (fun x => by rw [hF]; rfl) fun t => by
    rw [hF]
    exact RuR.ext rfl (by change t ^^^ (F 0).v = t; rw [h0, fin8_xor_zero])
  exact ⟨y.m, shearX_ext fun x => by rw [← hF, conj_eq_shearX]⟩

theorem dCode_mem (j : Fin 8) : dCode j ∈ glList := by
  revert j
  decide

theorem dCode_mul (i j : Fin 8) : ∃ l : Fin 8, linComp (dCode i) (dCode j) = dCode l := by
  revert i j
  decide

theorem dCode_inv (j : Fin 8) : ∃ l : Fin 8, linComp (dCode j) (dCode l) = linId := by
  revert j
  decide

theorem dCode_injective : Function.Injective dCode := by
  intro i j h
  revert i j
  decide

theorem dCode_zero : dCode 0 = linId := rfl

theorem dCode_dMul : ∀ d e : Fin 8, linComp (dCode d) (dCode e) = dCode (dMul d e) := by
  decide

theorem dMul_surj : ∀ d y : Fin 8, ∃ e, dMul d e = y := by decide

theorem nCo_nB : ∀ j < 8, nCo (nB j) = 2 ^ j := by decide

theorem xs8_two_pow (f : ℕ → Fin 8) {j : ℕ} (hj : j < 8) : xs8 (2 ^ j) f = f j := by
  simp only [xs8, Nat.testBit_two_pow]
  interval_cases j <;> simp [fin8_zero_xor]

theorem linExt_nB (lam : ℕ → Fin 8) {j : ℕ} (hj : j < 8) : linExt lam (nB j) = lam j := by
  rw [linExt, nCo_nB j hj, xs8_two_pow lam hj]

@[expose] def maskCoeff (y : Fin 8) (v : ℕ) : Bool := (nCo v).testBit y.val

theorem maskCoeff_xor (y : Fin 8) (v w : ℕ) :
    maskCoeff y (v ^^^ w) = (maskCoeff y v ^^ maskCoeff y w) := by
  simp only [maskCoeff, nCo_xor, Nat.testBit_xor]

theorem maskCoeff_zero (y : Fin 8) : maskCoeff y 0 = false := by
  simp only [maskCoeff, nCo_zero, Nat.zero_testBit]

theorem maskCoeff_nB : ∀ x < 8, ∀ y : Fin 8, maskCoeff y (nB x) = decide (x = y.val) := by
  decide

theorem maskCoeff_nAd_nB : ∀ d e : Fin 8, ∀ j < 8,
    maskCoeff (dMul d e) (nAd (dCode d) (nB j)) = maskCoeff e (nB j) := by
  decide

theorem maskCoeff_selB (y : Fin 8) (b : Bool) (c : ℕ) :
    maskCoeff y (selB b c) = (b && maskCoeff y c) := by
  cases b <;> simp [selB, maskCoeff_zero]

@[expose] def maskOf (f : Fin 8 → Bool) : ℕ :=
  selB (f 0) (nB 0) ^^^ selB (f 1) (nB 1) ^^^ selB (f 2) (nB 2) ^^^ selB (f 3) (nB 3) ^^^
    selB (f 4) (nB 4) ^^^ selB (f 5) (nB 5) ^^^ selB (f 6) (nB 6) ^^^ selB (f 7) (nB 7)

theorem maskOf_lt (f : Fin 8 → Bool) : maskOf f < 256 := by
  unfold maskOf
  repeat' first | apply xor_lt | exact selB_lt _ (nB_lt (by decide))

theorem maskCoeff_maskOf (f : Fin 8 → Bool) (y : Fin 8) : maskCoeff y (maskOf f) = f y := by
  simp only [maskOf, maskCoeff_xor, maskCoeff_selB, maskCoeff_nB 0 (by decide),
    maskCoeff_nB 1 (by decide), maskCoeff_nB 2 (by decide), maskCoeff_nB 3 (by decide),
    maskCoeff_nB 4 (by decide), maskCoeff_nB 5 (by decide), maskCoeff_nB 6 (by decide),
    maskCoeff_nB 7 (by decide)]
  fin_cases y <;> simp

section Cert


theorem eq_zero_of_innerS_eq_zero {m : Fin 256} (h : innerS m = 0) : m = 0 := by
  have hc : (⟨m, 0⟩ : RuR) ∈ center RuR := by
    refine mem_center_iff.mpr fun g => RuR.ext ?_ ?_
    · change g.m ^^^ m = m ^^^ g.m
      exact Fin.ext (by rw [fin256_val_xor, fin256_val_xor, Nat.xor_comm])
    · have hg : nBeta m.val g.m.val ^^^ nBeta g.m.val m.val = 0 :=
        congrArg X8.v (congrFun h g.m)
      change g.t ^^^ 0 ^^^ nBeta g.m.val m.val = (0 : Fin 8) ^^^ g.t ^^^ nBeta m.val g.m.val
      rw [fin8_xor_zero, fin8_zero_xor, fin8_eq_of_xor_eq_zero hg]
  rw [center_RuR] at hc
  exact hc

theorem innerS_injective {m m' : Fin 256} (h : innerS m = innerS m') : m = m' := by
  have h0 := eq_zero_of_innerS_eq_zero (show innerS (m ^^^ m') = 0 by
    rw [innerS_xor, h, fadd_self])
  have h1 : m.val ^^^ m'.val = 0 :=
    (fin256_val_xor m m').symm.trans ((congrArg Fin.val h0).trans rfl)
  apply Fin.ext
  have h2 := congrArg (· ^^^ m'.val) h1
  simpa [Nat.xor_assoc] using h2

theorem maskCoeff_ext {v w : ℕ} (hv : v < 256) (hw : w < 256)
    (h : ∀ y, maskCoeff y v = maskCoeff y w) : v = w := by
  have hco : ∀ u, nCo u < 256 := fun u => maskApply_lt (by decide) u
  have e : nCo v = nCo w := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases hi : i < 8
    · exact h ⟨i, hi⟩
    · have h8 : 256 ≤ 2 ^ i :=
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hco v) h8),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hco w) h8)]
  rw [← (nIdCheck_parts.1 v hv).2.2, ← (nIdCheck_parts.1 w hw).2.2, e]

theorem maskCoeff_nAd (d e : Fin 8) {v : ℕ} (hv : v < 256) :
    maskCoeff (dMul d e) (nAd (dCode d) v) = maskCoeff e v := by
  refine mask_induction (P := fun v => maskCoeff (dMul d e) (nAd (dCode d) v) = maskCoeff e v)
    ?_ ?_ hv
  · simp only [nAd_zero, maskCoeff_zero]
  · intro m _ j hj ih
    simp only [nAd_xor, maskCoeff_xor, ih, maskCoeff_nAd_nB d e j hj]

theorem d8_coboundary (m : Fin 8 → ℕ) (hm : ∀ d, m d < 256)
    (hc : ∀ d e, m (dMul d e) = m d ^^^ nAd (dCode d) (m e)) :
    ∃ ι < 256, ∀ d, m d = ι ^^^ nAd (dCode d) ι := by
  refine ⟨maskOf fun y => maskCoeff y (m y), maskOf_lt _, fun d => ?_⟩
  refine maskCoeff_ext (hm d) (xor_lt (maskOf_lt _) (nAd_lt _ _)) fun y => ?_
  obtain ⟨e, rfl⟩ := dMul_surj d y
  have h := congrArg (maskCoeff (dMul d e)) (hc d e)
  rw [maskCoeff_xor, maskCoeff_nAd d e (hm e)] at h
  rw [maskCoeff_xor, maskCoeff_nAd d e (maskOf_lt _), maskCoeff_maskOf, maskCoeff_maskOf, h,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

@[expose] noncomputable def codeOf (k : nK) : Lin8 := Classical.choose k.2

theorem codeOf_mem (k : nK) : codeOf k ∈ glList := (Classical.choose_spec k.2).1

theorem codeOf_spec (k : nK) (x : RuR) : (k : MulAut RuR) x = nAut (codeOf k) x :=
  (Classical.choose_spec k.2).2 x

theorem inv_apply_eq (k : nK) (y : RuR) :
    ((k : MulAut RuR)⁻¹) y = nAut (linInv (codeOf k)) y := by
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, codeOf_spec,
    nAut_linComp (codeOf_mem k) (linInv_mem (codeOf_mem k)),
    linComp_self_linInv (codeOf_mem k), nAut_linId]

@[expose] noncomputable def act (k : nK) (F : Fin 256 → Fin 8) (n : Fin 256) : Fin 8 :=
  linApply (codeOf k) (F ⟨nAd (linInv (codeOf k)) n.val, nAd_lt _ _⟩)

theorem conj_shear (k : nK) (F : Fin 256 → Fin 8) (y : RuR) :
    (k : MulAut RuR) (shear F (((k : MulAut RuR)⁻¹) y)) = shear (act k F) y := by
  set x := ((k : MulAut RuR)⁻¹) y with hx
  have hy : (k : MulAut RuR) x = y := by rw [hx, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hxm : x.m = ⟨nAd (linInv (codeOf k)) y.m.val, nAd_lt _ _⟩ := by
    apply Fin.ext
    rw [hx, inv_apply_eq, nAut_m]
  rw [shear_eq_mul, map_mul, hy, codeOf_spec k ⟨0, F x.m⟩, nAut_A1, mul_A1, shear, act, hxm]

@[expose] noncomputable def actX (k : nK) : (Fin 256 → X8) →+ (Fin 256 → X8) where
  toFun F n := ⟨act k (fun i => (F i).v) n⟩
  map_zero' := by
    funext n
    refine X8.ext ?_
    change linApply (codeOf k) 0 = 0
    rw [linApply_zero]
  map_add' F G := by
    funext n
    refine X8.ext ?_
    change act k (fun i => (F i).v ^^^ (G i).v) n =
      act k (fun i => (F i).v) n ^^^ act k (fun i => (G i).v) n
    simp only [act, linApply_xor]

theorem apply_shearX (k : nK) (F : Fin 256 → X8) (x : RuR) :
    (k : MulAut RuR) (shearX F x) = shearX (actX k F) ((k : MulAut RuR) x) := by
  have h := conj_shear k (fun n => (F n).v) ((k : MulAut RuR) x)
  rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h
  exact h

theorem actX_mul (k k' : nK) (F : Fin 256 → X8) : actX (k * k') F = actX k (actX k' F) := by
  refine shearX_ext fun y => ?_
  obtain ⟨x, rfl⟩ := ((k * k' : nK) : MulAut RuR).surjective y
  rw [← apply_shearX, Subgroup.coe_mul, MulAut.mul_apply, MulAut.mul_apply, apply_shearX,
    apply_shearX]

theorem actX_innerS (k : nK) (m : Fin 256) :
    actX k (innerS m) = innerS ((k : MulAut RuR) ⟨m, 0⟩).m := by
  refine shearX_ext fun y => ?_
  obtain ⟨x, rfl⟩ := (k : MulAut RuR).surjective y
  have h1 : (k : MulAut RuR) (MulAut.conj (⟨m, 0⟩ : RuR) x) =
      MulAut.conj ((k : MulAut RuR) ⟨m, 0⟩) ((k : MulAut RuR) x) := by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [conj_eq_shearX, conj_eq_shearX, apply_shearX] at h1
  exact h1

@[expose] noncomputable def nD : Subgroup nK where
  carrier := {k | ∃ j : Fin 8, ∀ x, (k : MulAut RuR) x = nAut (dCode j) x}
  mul_mem' := by
    rintro k k' ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨l, hl⟩ := dCode_mul i j
    refine ⟨l, fun x => ?_⟩
    rw [Subgroup.coe_mul, MulAut.mul_apply, hj, hi,
      nAut_linComp (dCode_mem i) (dCode_mem j), hl]
  one_mem' := ⟨0, fun x => by
    rw [Subgroup.coe_one, MulAut.one_apply, dCode_zero, nAut_linId]⟩
  inv_mem' := by
    rintro k ⟨j, hj⟩
    obtain ⟨l, hl⟩ := dCode_inv j
    refine ⟨l, fun x => ?_⟩
    rw [Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, hj,
      nAut_linComp (dCode_mem j) (dCode_mem l), hl, nAut_linId]

theorem card_nD : Nat.card nD = 8 := by
  classical
  let F : Fin 8 → nD := fun j => ⟨⟨nAutE (dCode_mem j), dCode j, dCode_mem j, fun _ => rfl⟩,
    j, fun _ => rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun i j h => dCode_injective (eq_of_nAut_eq fun x => ?_), fun k => ?_⟩
    · exact congrArg (fun k : nD => ((k : nK) : MulAut RuR) x) h
    · obtain ⟨j, hj⟩ := k.2
      exact ⟨j, Subtype.ext (Subtype.ext (MulEquiv.ext fun x => (hj x).symm))⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem index_nD : nD.index = 21 := by
  have h := Subgroup.card_mul_index nD
  rw [card_nD, card_nK] at h
  omega

@[expose] noncomputable def dK (j : Fin 8) : nK :=
  ⟨nAutE (dCode_mem j), dCode j, dCode_mem j, fun _ => rfl⟩

theorem dK_apply (j : Fin 8) (x : RuR) : (dK j : MulAut RuR) x = nAut (dCode j) x := rfl

theorem dK_mem (j : Fin 8) : dK j ∈ nD := ⟨j, fun _ => rfl⟩

theorem dK_mul (d e : Fin 8) : dK d * dK e = dK (dMul d e) := by
  refine Subtype.ext (MulEquiv.ext fun x => ?_)
  rw [Subgroup.coe_mul, MulAut.mul_apply, dK_apply, dK_apply, dK_apply,
    nAut_linComp (dCode_mem d) (dCode_mem e), dCode_dMul]

theorem eq_dK {k : nK} {j : Fin 8} (hj : ∀ x, (k : MulAut RuR) x = nAut (dCode j) x) :
    k = dK j :=
  Subtype.ext (MulEquiv.ext hj)

theorem exists_inner_d8 (c : nK → (Fin 256 → X8)) (hcI : ∀ p ∈ nD, c p ∈ innerI)
    (hcoc : ∀ p ∈ nD, ∀ q ∈ nD, c (p * q) = c p + actX p (c q)) :
    ∃ ι : Fin 256, ∀ p ∈ nD, c p = innerS ι + actX p (innerS ι) := by
  choose m hm using fun j : Fin 8 => (mem_innerI_iff _).mp (hcI (dK j) (dK_mem j))
  have hmc : ∀ d e, (m (dMul d e)).val = (m d).val ^^^ nAd (dCode d) (m e).val := by
    intro d e
    have h := hcoc (dK d) (dK_mem d) (dK e) (dK_mem e)
    rw [dK_mul, hm, hm, hm, actX_innerS, ← innerS_xor] at h
    have e1 : (m d ^^^ ((dK d : MulAut RuR) ⟨m e, 0⟩).m).val =
        (m d).val ^^^ nAd (dCode d) (m e).val := fin256_val_xor _ _
    exact (congrArg Fin.val (innerS_injective h)).trans e1
  obtain ⟨ι, hι, hιc⟩ := d8_coboundary (fun j => (m j).val) (fun j => (m j).isLt) hmc
  refine ⟨⟨ι, hι⟩, fun p hp => ?_⟩
  obtain ⟨j, hj⟩ := hp
  rw [eq_dK hj, hm, actX_innerS, ← innerS_xor]
  have e1 : ((⟨ι, hι⟩ : Fin 256) ^^^ ((dK j : MulAut RuR) ⟨⟨ι, hι⟩, 0⟩).m).val =
      ι ^^^ nAd (dCode j) ι := fin256_val_xor _ _
  exact congrArg innerS (Fin.ext ((hιc j).trans e1.symm))

variable (ψ : nK → MulAut RuR)

@[expose] noncomputable def twAut (k : nK) : MulAut RuR := ψ k * (k : MulAut RuR)⁻¹

@[expose] noncomputable def twist (k : nK) : Fin 256 → Fin 8 := shearOf (twAut ψ k)

@[expose] noncomputable def twistX (k : nK) : Fin 256 → X8 := fun n => ⟨twist ψ k n⟩

@[expose] noncomputable def transferΛ [Fintype (nK ⧸ nD)] : Fin 256 → X8 :=
  ∑ q : nK ⧸ nD, twistX ψ q.out

variable {ψ}

theorem twAut_m (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m) (k : nK) (y : RuR) :
    (twAut ψ k y).m = y.m := by
  rw [twAut, MulAut.mul_apply, hm, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem twAut_A1 (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k : nK)
    (t : Fin 8) : twAut ψ k ⟨0, t⟩ = ⟨0, t⟩ := by
  rw [twAut, MulAut.mul_apply, inv_apply_eq, nAut_A1, hA, codeOf_spec, nAut_A1,
    ← linApply_linComp, linComp_self_linInv (codeOf_mem k), linApply_linId]

theorem psi_apply (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k : nK) (x : RuR) :
    ψ k x = shear (twist ψ k) ((k : MulAut RuR) x) := by
  have h := apply_eq_shear (twAut_m hm k) (twAut_A1 hA k) ((k : MulAut RuR) x)
  rw [twAut, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h
  exact h

theorem psi_applyX (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k : nK) (x : RuR) :
    ψ k x = shearX (twistX ψ k) ((k : MulAut RuR) x) :=
  psi_apply hm hA k x

theorem twist_xor (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k : nK) (n n' : Fin 256) :
    twist ψ k (n ^^^ n') = twist ψ k n ^^^ twist ψ k n' :=
  shearOf_xor (twAut_m hm k) (twAut_A1 hA k) n n'

theorem mul_mul_inv_apply (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k k' : nK) (x : RuR) :
    (ψ k * ψ k' * (ψ (k * k'))⁻¹) x =
      shearX (twistX ψ (k * k') + actX k (twistX ψ k') + twistX ψ k) x := by
  set w := (ψ (k * k'))⁻¹ x with hw
  have h1 : ψ (k * k') w = x := by rw [hw, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  rw [psi_applyX hm hA] at h1
  have h2 : ((k * k' : nK) : MulAut RuR) w = shearX (twistX ψ (k * k')) x := by
    rw [← h1, shearX_shearX, fadd_self, shearX_zero]
  have h3 : (k : MulAut RuR) ((k' : MulAut RuR) w) = ((k * k' : nK) : MulAut RuR) w := by
    rw [Subgroup.coe_mul, MulAut.mul_apply]
  rw [MulAut.mul_apply, MulAut.mul_apply, ← hw, psi_applyX hm hA k', psi_applyX hm hA k,
    apply_shearX, h3, h2, shearX_shearX, shearX_shearX, add_assoc]

theorem twistX_mul (hmul : ∀ k k' : nK, ψ (k * k') = ψ k * ψ k')
    (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (k k' : nK) :
    twistX ψ (k * k') = twistX ψ k + actX k (twistX ψ k') := by
  have h : twistX ψ (k * k') + actX k (twistX ψ k') + twistX ψ k = 0 := shearX_ext fun x => by
    rw [← mul_mul_inv_apply hm hA k k' x, hmul, mul_inv_cancel, MulAut.one_apply, shearX_zero]
  calc twistX ψ (k * k') = twistX ψ (k * k') + (actX k (twistX ψ k') + twistX ψ k) +
        (actX k (twistX ψ k') + twistX ψ k) := by rw [add_assoc, fadd_self, add_zero]
    _ = twistX ψ k + actX k (twistX ψ k') := by
      rw [← add_assoc (twistX ψ (k * k')) (actX k (twistX ψ k')) (twistX ψ k), h, zero_add,
        add_comm]

theorem twistX_eq_zero {p : nK} (hp : ψ p = p) : twistX ψ p = 0 := by
  funext n
  have h : twAut ψ p = 1 := by rw [twAut, hp, mul_inv_cancel]
  refine X8.ext ?_
  change twist ψ p n = 0
  rw [twist, shearOf, h, MulAut.one_apply]

theorem transfer_mem [Fintype (nK ⧸ nD)] (I : AddSubgroup (Fin 256 → X8))
    (hcoc : ∀ k k' : nK, twistX ψ (k * k') + twistX ψ k + actX k (twistX ψ k') ∈ I)
    (h0 : ∀ p ∈ nD, twistX ψ p = 0) (g : nK) :
    twistX ψ g + transferΛ ψ + actX g (transferΛ ψ) ∈ I := by
  have hU : ∀ q : nK ⧸ nD, twistX ψ (g * q.out) + twistX ψ (g • q).out ∈ I := by
    intro q
    have hmem : ((g • q).out)⁻¹ * (g * q.out) ∈ nD := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    have h := hcoc (g • q).out (((g • q).out)⁻¹ * (g * q.out))
    rwa [← e, h0 _ hmem, map_zero, add_zero] at h
  have hT : ∀ q : nK ⧸ nD,
      actX g (twistX ψ q.out) + twistX ψ (g * q.out) + twistX ψ g ∈ I := by
    intro q
    have h := hcoc g q.out
    rwa [add_comm, ← add_assoc] at h
  have hsum : ∑ q : nK ⧸ nD, twistX ψ (g • q).out = transferΛ ψ :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : nK ⧸ nD => twistX ψ q.out)
  have hcard : Fintype.card (nK ⧸ nD) = 2 * 10 + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index, index_nD]
  have hq : ∀ q : nK ⧸ nD, actX g (twistX ψ q.out) + twistX ψ (g * q.out) + twistX ψ g +
      (twistX ψ (g * q.out) + twistX ψ (g • q).out) =
      actX g (twistX ψ q.out) + twistX ψ (g • q).out + twistX ψ g := by
    intro q
    rw [show actX g (twistX ψ q.out) + twistX ψ (g * q.out) + twistX ψ g +
        (twistX ψ (g * q.out) + twistX ψ (g • q).out) =
        actX g (twistX ψ q.out) + twistX ψ (g • q).out + twistX ψ g +
        (twistX ψ (g * q.out) + twistX ψ (g * q.out)) by abel, fadd_self, add_zero]
  have e : twistX ψ g + transferΛ ψ + actX g (transferΛ ψ) =
      ∑ q : nK ⧸ nD, (actX g (twistX ψ q.out) + twistX ψ (g * q.out) + twistX ψ g +
        (twistX ψ (g * q.out) + twistX ψ (g • q).out)) := by
    rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← map_sum, hsum, Finset.sum_const, Finset.card_univ, hcard, odd_nsmul_eq, transferΛ]
    abel
  rw [e]
  exact AddSubgroup.sum_mem I fun q _ => add_mem (hT q) (hU q)

theorem twist_eq_zero
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) → ψ k = k)
    {p : nK} (hp : p ∈ nD) (n : Fin 256) : twist ψ p n = 0 := by
  obtain ⟨j, hj⟩ := hp
  have h : twAut ψ p = 1 := by rw [twAut, hD p j hj, mul_inv_cancel]
  rw [twist, shearOf, h, MulAut.one_apply]

theorem twist_eq_coboundary [Fintype (nK ⧸ nD)] (hmul : ∀ k k' : nK, ψ (k * k') = ψ k * ψ k')
    (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩)
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) → ψ k = k)
    (g : nK) : twistX ψ g = transferΛ ψ + actX g (transferΛ ψ) := by
  have h := transfer_mem ⊥ (fun k k' => by
      rw [twistX_mul hmul hm hA, AddSubgroup.mem_bot,
        show twistX ψ k + actX k (twistX ψ k') + twistX ψ k + actX k (twistX ψ k') =
          twistX ψ k + twistX ψ k + (actX k (twistX ψ k') + actX k (twistX ψ k')) by abel,
        fadd_self, fadd_self, add_zero])
    (fun p hp => funext fun n => X8.ext (twist_eq_zero hD hp n)) g
  rw [AddSubgroup.mem_bot] at h
  calc twistX ψ g = twistX ψ g + (transferΛ ψ + actX g (transferΛ ψ)) +
        (transferΛ ψ + actX g (transferΛ ψ)) := by rw [add_assoc, fadd_self, add_zero]
    _ = transferΛ ψ + actX g (transferΛ ψ) := by rw [← add_assoc (twistX ψ g), h, zero_add]

theorem transferΛ_xor [Fintype (nK ⧸ nD)]
    (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) (n n' : Fin 256) :
    transferΛ ψ (n ^^^ n') = transferΛ ψ n + transferΛ ψ n' := by
  simp only [transferΛ, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => X8.ext (twist_xor hm hA _ n n')

theorem exists_lam_of_add (Λ : Fin 256 → X8) (hadd : ∀ n n', Λ (n ^^^ n') = Λ n + Λ n') :
    ∃ lam : ℕ → Fin 8, ∀ y, cAut lam y = shearX Λ y := by
  let lam : ℕ → Fin 8 := fun j => if h : j < 8 then (Λ ⟨nB j, nB_lt h⟩).v else 0
  have hlin : ∀ m : ℕ, ∀ hm' : m < 256, linExt lam m = (Λ ⟨m, hm'⟩).v := by
    intro m hm'
    refine mask_induction (P := fun m => ∀ hm' : m < 256, linExt lam m = (Λ ⟨m, hm'⟩).v)
      ?_ ?_ hm' hm'
    · intro h0
      have e := hadd 0 0
      rw [fin256_xor_zero, X8.add_self] at e
      rw [show (⟨0, h0⟩ : Fin 256) = 0 from rfl, e]
      simp [linExt, nCo_zero, xs8_zero, X8.v_zero]
    · intro m hm2 j hj ih hmj
      have hb := nB_lt hj
      have e := hadd ⟨m, hm2⟩ ⟨nB j, hb⟩
      have hval : (⟨m, hm2⟩ ^^^ ⟨nB j, hb⟩ : Fin 256) = ⟨m ^^^ nB j, hmj⟩ :=
        Fin.ext (fin256_val_xor _ _)
      rw [hval] at e
      rw [linExt_xor, ih hm2, linExt_nB lam hj, e, X8.v_add]
      simp only [lam, hj, ↓reduceDIte]
  exact ⟨lam, fun y => RuR.ext rfl (by rw [cAut_apply, hlin y.m.val y.m.isLt]; rfl)⟩

theorem exists_cAut_conj (ψ : nK →* MulAut RuR)
    (hm : ∀ k : nK, ∀ x, (ψ k x).m = ((k : MulAut RuR) x).m)
    (hA : ∀ k : nK, ∀ t, ψ k ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩)
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) → ψ k = k) :
    ∃ lam : ℕ → Fin 8, ∀ k : nK, ψ k = cAut lam * (k : MulAut RuR) * cAut lam := by
  classical
  have : Finite nK := Nat.finite_of_card_ne_zero (by rw [card_nK]; norm_num)
  have : Fintype (nK ⧸ nD) := Fintype.ofFinite _
  obtain ⟨lam, hcA⟩ := exists_lam_of_add (transferΛ ψ) (transferΛ_xor hm hA)
  refine ⟨lam, fun g => MulEquiv.ext fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hcA x, apply_shearX, hcA, shearX_shearX,
    psi_applyX hm hA g x, twist_eq_coboundary (map_mul ψ) hm hA hD g, add_comm]

theorem exists_lift (M : Subgroup (MulAut RuR))
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
      (k : MulAut RuR) ∈ M)
    (hall : ∀ r ∈ glList, ∃ f ∈ M, (∀ x, (f x).m = (nAut r x).m) ∧
      ∀ t, f ⟨0, t⟩ = ⟨0, linApply r t⟩) (k : nK) :
    ∃ f ∈ M, (∀ x, (f x).m = ((k : MulAut RuR) x).m) ∧
      (∀ t, f ⟨0, t⟩ = (k : MulAut RuR) ⟨0, t⟩) ∧ (k ∈ nD → f = k) := by
  by_cases hk : k ∈ nD
  · obtain ⟨j, hj⟩ := hk
    exact ⟨k, hD k j hj, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨f, hf, hfm, hfA⟩ := hall (codeOf k) (codeOf_mem k)
    refine ⟨f, hf, fun x => by rw [hfm, codeOf_spec], fun t => ?_, fun h => absurd h hk⟩
    rw [hfA, codeOf_spec, nAut_A1]

theorem exists_cAut_conj_mem (M : Subgroup (MulAut RuR))
    (hInn : ∀ y : RuR, MulAut.conj y ∈ M)
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
      (k : MulAut RuR) ∈ M)
    (hall : ∀ r ∈ glList, ∃ f ∈ M, (∀ x, (f x).m = (nAut r x).m) ∧
      ∀ t, f ⟨0, t⟩ = ⟨0, linApply r t⟩)
    (hker : ∀ f ∈ M, (∀ x, (f x).m = x.m) → (∀ t, f ⟨0, t⟩ = ⟨0, t⟩) →
      ∃ y, f = MulAut.conj y) :
    ∃ lam : ℕ → Fin 8, (∀ k : nK, cAut lam * (k : MulAut RuR) * cAut lam ∈ M) ∧
      ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
        cAut lam * (k : MulAut RuR) * cAut lam = k := by
  classical
  have : Finite nK := Nat.finite_of_card_ne_zero (by rw [card_nK]; norm_num)
  have : Fintype (nK ⧸ nD) := Fintype.ofFinite _
  choose f hfM hfm hfA hfD using exists_lift M hD hall
  have hcoc : ∀ k k' : nK,
      twistX f (k * k') + twistX f k + actX k (twistX f k') ∈ innerI := by
    intro k k'
    have h := mem_innerI_of_shearX hker
      (M.mul_mem (M.mul_mem (hfM k) (hfM k')) (M.inv_mem (hfM (k * k'))))
      (mul_mul_inv_apply hfm hfA k k')
    rwa [add_right_comm] at h
  have h0 : ∀ p ∈ nD, twistX f p = 0 := fun p hp => twistX_eq_zero (hfD p hp)
  have hΛ : ∀ g : nK, twistX f g + transferΛ f + actX g (transferΛ f) ∈ innerI :=
    transfer_mem innerI hcoc h0
  have hΛadd := transferΛ_xor hfm hfA
  generalize transferΛ f = Λ at hΛ hΛadd
  obtain ⟨ι, hι⟩ := exists_inner_d8 (fun p => Λ + actX p Λ)
    (fun p hp => by simpa only [h0 p hp, zero_add] using hΛ p) fun p _ q _ => by
      simp only [actX_mul, map_add]
      rw [show Λ + actX p Λ + (actX p Λ + actX p (actX q Λ)) =
        Λ + actX p (actX q Λ) + (actX p Λ + actX p Λ) by abel, fadd_self, add_zero]
  obtain ⟨lam, hcA⟩ := exists_lam_of_add (Λ + innerS ι) fun n n' => by
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, hΛadd, innerS_apply_xor]
    abel
  have hconj : ∀ k : nK, ∀ x, (cAut lam * (k : MulAut RuR) * cAut lam) x =
      shearX (actX k (Λ + innerS ι) + (Λ + innerS ι)) ((k : MulAut RuR) x) := by
    intro k x
    rw [MulAut.mul_apply, MulAut.mul_apply, hcA x, apply_shearX, hcA, shearX_shearX]
  refine ⟨lam, fun k => ?_, fun k j hj => MulEquiv.ext fun x => ?_⟩
  · have hmem : twistX f k + (Λ + innerS ι) + actX k (Λ + innerS ι) ∈ innerI := by
      have e : twistX f k + (Λ + innerS ι) + actX k (Λ + innerS ι) =
          twistX f k + Λ + actX k Λ + (innerS ι + actX k (innerS ι)) := by
        rw [map_add]
        abel
      rw [e, actX_innerS]
      exact add_mem (hΛ k) (add_mem (innerS_mem _) (innerS_mem _))
    obtain ⟨m, hm⟩ := (mem_innerI_iff _).mp hmem
    have e : cAut lam * (k : MulAut RuR) * cAut lam = MulAut.conj (⟨m, 0⟩ : RuR) * f k := by
      refine MulEquiv.ext fun x => ?_
      rw [hconj, MulAut.mul_apply, conj_eq_shearX, psi_applyX hfm hfA k x, shearX_shearX]
      congr 1
      change _ = twistX f k + innerS m
      rw [← hm, show twistX f k + (twistX f k + (Λ + innerS ι) + actX k (Λ + innerS ι)) =
        twistX f k + twistX f k + (actX k (Λ + innerS ι) + (Λ + innerS ι)) by abel,
        fadd_self, zero_add]
    rw [e]
    exact M.mul_mem (hInn _) (hfM k)
  · have h1 : Λ + actX k Λ = innerS ι + actX k (innerS ι) := hι k ⟨j, hj⟩
    have h2 : actX k (Λ + innerS ι) + (Λ + innerS ι) = 0 := by
      rw [map_add, show actX k Λ + actX k (innerS ι) + (Λ + innerS ι) =
        Λ + actX k Λ + (innerS ι + actX k (innerS ι)) by abel, h1, fadd_self]
    rw [hconj, h2, shearX_zero]

theorem exists_conj_mem (M : Subgroup (MulAut RuR))
    (hInn : ∀ y : RuR, MulAut.conj y ∈ M)
    (hD : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
      (k : MulAut RuR) ∈ M)
    (hall : ∀ r ∈ glList, ∃ f ∈ M, (∀ x, (f x).m = (nAut r x).m) ∧
      ∀ t, f ⟨0, t⟩ = ⟨0, linApply r t⟩)
    (hker : ∀ f ∈ M, (∀ x, (f x).m = x.m) → (∀ t, f ⟨0, t⟩ = ⟨0, t⟩) →
      ∃ y, f = MulAut.conj y) :
    ∃ c : MulAut RuR, c * c = 1 ∧ (∀ x, (c x).m = x.m) ∧ (∀ t, c ⟨0, t⟩ = ⟨0, t⟩) ∧
      (∀ k : nK, c * (k : MulAut RuR) * c ∈ M) ∧
      ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
        c * (k : MulAut RuR) * c = k := by
  obtain ⟨lam, h1, h2⟩ := exists_cAut_conj_mem M hInn hD hall hker
  exact ⟨cAut lam, cAut_mul_self lam, cAut_m lam, cAut_A1 lam, h1, h2⟩

end Cert

end CFSG.ComponentClassification.GMS78.RuN
