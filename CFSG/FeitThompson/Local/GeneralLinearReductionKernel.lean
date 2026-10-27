module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.NoncommRing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix

section ZMod

variable (p e : ℕ)

def zmodMulPow : ZMod p →+ ZMod (p ^ (e + 1)) :=
  ZMod.lift p ⟨(AddMonoidHom.mulLeft ((p : ZMod (p ^ (e + 1))) ^ e)).comp
      (Int.castAddHom (ZMod (p ^ (e + 1)))), by
    have h : ((p ^ (e + 1) : ℕ) : ZMod (p ^ (e + 1))) = 0 := ZMod.natCast_self _
    push_cast at h
    simpa [← pow_succ] using h⟩

@[simp] lemma zmodMulPow_intCast (m : ℤ) :
    zmodMulPow p e (m : ZMod p) = (p : ZMod (p ^ (e + 1))) ^ e * (m : ZMod (p ^ (e + 1))) := by
  simp [zmodMulPow, ZMod.lift_coe]

@[simp] lemma zmodMulPow_natCast (m : ℕ) :
    zmodMulPow p e (m : ZMod p) = (p : ZMod (p ^ (e + 1))) ^ e * (m : ZMod (p ^ (e + 1))) := by
  have := zmodMulPow_intCast p e (m : ℤ)
  push_cast at this
  exact this

lemma zmodMulPow_injective [NeZero p] : Function.Injective (zmodMulPow p e) := by
  rw [zmodMulPow, ZMod.lift_injective]
  intro m hm
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mulLeft, Function.comp_apply,
    Int.coe_castAddHom] at hm
  have h : ((p ^ e * m : ℤ) : ZMod (p ^ (e + 1))) = 0 := by push_cast; exact hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hp : (p : ℤ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne p)
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left hp).mp h

lemma zmodMulPow_mul_zmodMulPow (he : 1 ≤ e) (a b : ZMod p) :
    zmodMulPow p e a * zmodMulPow p e b = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : ZMod p) = a := ⟨a.cast, ZMod.intCast_zmod_cast a⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ZMod p) = b := ⟨b.cast, ZMod.intCast_zmod_cast b⟩
  have h : ((p : ZMod (p ^ (e + 1)))) ^ (e + e) = 0 := by
    have h' : ((p ^ (e + e) : ℕ) : ZMod (p ^ (e + 1))) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p (by omega)
    push_cast at h'
    exact h'
  rw [zmodMulPow_intCast, zmodMulPow_intCast]
  calc (p : ZMod (p ^ (e + 1))) ^ e * (m : ZMod (p ^ (e + 1)))
        * ((p : ZMod (p ^ (e + 1))) ^ e * (n : ZMod (p ^ (e + 1))))
      = (p : ZMod (p ^ (e + 1))) ^ (e + e)
        * ((m : ZMod (p ^ (e + 1))) * (n : ZMod (p ^ (e + 1)))) := by ring
    _ = 0 := by rw [h, zero_mul]

abbrev zmodReduction : ZMod (p ^ (e + 1)) →+* ZMod (p ^ e) :=
  ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e))

@[simp] lemma zmodReduction_zmodMulPow (a : ZMod p) :
    zmodReduction p e (zmodMulPow p e a) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : ZMod p) = a := ⟨a.cast, ZMod.intCast_zmod_cast a⟩
  have h : ((p : ZMod (p ^ e))) ^ e = 0 := by
    have h' : ((p ^ e : ℕ) : ZMod (p ^ e)) = 0 := ZMod.natCast_self _
    push_cast at h'
    exact h'
  rw [zmodMulPow_intCast, map_mul, map_pow, map_natCast, h, zero_mul]

lemma exists_zmodMulPow_eq [NeZero p] {a : ZMod (p ^ (e + 1))} (ha : zmodReduction p e a = 0) :
    ∃ b : ZMod p, zmodMulPow p e b = a := by
  have : NeZero (p ^ (e + 1)) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  rw [zmodReduction, ZMod.castHom_apply, ← ZMod.natCast_val a, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨k, hk⟩ := ha
  refine ⟨(k : ZMod p), ?_⟩
  have ha' : ((a.val : ℕ) : ZMod (p ^ (e + 1))) = a := by rw [ZMod.natCast_val, ZMod.cast_id]
  rw [zmodMulPow_natCast, ← ha', hk]
  push_cast
  ring

end ZMod

def matrixMulPow (ι : Type*) (p e : ℕ) :
    Matrix ι ι (ZMod p) →+ Matrix ι ι (ZMod (p ^ (e + 1))) :=
  (zmodMulPow p e).mapMatrix

variable {ι : Type*} {p e : ℕ}

@[simp] lemma matrixMulPow_apply (X : Matrix ι ι (ZMod p)) (i j : ι) :
    matrixMulPow ι p e X i j = zmodMulPow p e (X i j) := (rfl)

lemma matrixMulPow_injective [NeZero p] : Function.Injective (matrixMulPow ι p e) := by
  intro X Y h
  ext i j
  exact zmodMulPow_injective p e (by simpa using congrFun (congrFun h i) j)

lemma matrixMulPow_mul_matrixMulPow [Fintype ι] (he : 1 ≤ e) (X Y : Matrix ι ι (ZMod p)) :
    matrixMulPow ι p e X * matrixMulPow ι p e Y = 0 := by
  ext i j
  simp [Matrix.mul_apply, zmodMulPow_mul_zmodMulPow p e he]

def glPowReduction (ι : Type*) [Fintype ι] [DecidableEq ι] (p e : ℕ) :
    GL ι (ZMod (p ^ (e + 1))) →* GL ι (ZMod (p ^ e)) :=
  Matrix.GeneralLinearGroup.map (zmodReduction p e)

variable [Fintype ι] [DecidableEq ι]

lemma coe_glPowReduction (g : GL ι (ZMod (p ^ (e + 1)))) :
    (glPowReduction ι p e g : Matrix ι ι (ZMod (p ^ e)))
      = (g : Matrix ι ι (ZMod (p ^ (e + 1)))).map (zmodReduction p e) := by
  ext i j
  rw [glPowReduction, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]

theorem mem_ker_glPowReduction_iff [NeZero p] (g : GL ι (ZMod (p ^ (e + 1)))) :
    g ∈ (glPowReduction ι p e).ker ↔
      ∃ X : Matrix ι ι (ZMod p),
        (g : Matrix ι ι (ZMod (p ^ (e + 1)))) = 1 + matrixMulPow ι p e X := by
  rw [MonoidHom.mem_ker, ← Units.val_inj, coe_glPowReduction, Units.val_one,
    ← sub_eq_zero (a := ((g : Matrix ι ι (ZMod (p ^ (e + 1))))).map (zmodReduction p e)),
    ← Matrix.map_one (zmodReduction p e) (map_zero _) (map_one _),
    ← Matrix.map_sub _ (map_sub _)]
  constructor
  · intro h
    have h' : ∀ i j, ∃ b : ZMod p,
        zmodMulPow p e b = ((g : Matrix ι ι (ZMod (p ^ (e + 1)))) - 1) i j := fun i j =>
      exists_zmodMulPow_eq p e (by simpa [Matrix.map_apply] using congrFun (congrFun h i) j)
    choose X hX using h'
    refine ⟨Matrix.of X, ?_⟩
    ext i j
    rw [Matrix.add_apply, matrixMulPow_apply, Matrix.of_apply, hX i j, Matrix.sub_apply]
    ring
  · rintro ⟨X, hX⟩
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, hX, Matrix.add_apply]
    simp only [add_sub_cancel_left, matrixMulPow_apply, zmodReduction_zmodMulPow]
    rfl

def onePlusMatrixMulPow [NeZero p] (he : 1 ≤ e) :
    Multiplicative (Matrix ι ι (ZMod p)) →* (glPowReduction ι p e).ker where
  toFun X := ⟨⟨1 + matrixMulPow ι p e X.toAdd, 1 - matrixMulPow ι p e X.toAdd,
      by noncomm_ring [matrixMulPow_mul_matrixMulPow he],
      by noncomm_ring [matrixMulPow_mul_matrixMulPow he]⟩,
    (mem_ker_glPowReduction_iff _).2 ⟨X.toAdd, rfl⟩⟩
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    change (1 : Matrix ι ι _) + matrixMulPow ι p e (0 : Matrix ι ι (ZMod p)) = 1
    simp
  map_mul' X Y := by
    refine Subtype.ext (Units.ext ?_)
    change (1 : Matrix ι ι _) + matrixMulPow ι p e (X.toAdd + Y.toAdd)
      = (1 + matrixMulPow ι p e X.toAdd) * (1 + matrixMulPow ι p e Y.toAdd)
    rw [map_add]
    noncomm_ring [matrixMulPow_mul_matrixMulPow he]

@[simp] lemma coe_coe_onePlusMatrixMulPow [NeZero p] (he : 1 ≤ e)
    (X : Multiplicative (Matrix ι ι (ZMod p))) :
    ((onePlusMatrixMulPow he X : GL ι (ZMod (p ^ (e + 1)))) : Matrix ι ι (ZMod (p ^ (e + 1))))
      = 1 + matrixMulPow ι p e X.toAdd := (rfl)

noncomputable def kerGlPowReductionMulEquiv [NeZero p] (he : 1 ≤ e) :
    Multiplicative (Matrix ι ι (ZMod p)) ≃* (glPowReduction ι p e).ker :=
  MulEquiv.ofBijective (onePlusMatrixMulPow he) <| by
    constructor
    · intro X Y h
      have h' := congrArg
        (fun g : (glPowReduction ι p e).ker => ((g : GL ι (ZMod (p ^ (e + 1)))) :
          Matrix ι ι (ZMod (p ^ (e + 1))))) h
      simp only [coe_coe_onePlusMatrixMulPow] at h'
      exact Multiplicative.toAdd.injective (matrixMulPow_injective (add_left_cancel h'))
    · rintro ⟨g, hg⟩
      obtain ⟨X, hX⟩ := (mem_ker_glPowReduction_iff g).1 hg
      exact ⟨Multiplicative.ofAdd X, Subtype.ext (Units.ext (by simpa using hX.symm))⟩

@[simp] lemma coe_coe_kerGlPowReductionMulEquiv [NeZero p] (he : 1 ≤ e)
    (X : Multiplicative (Matrix ι ι (ZMod p))) :
    ((kerGlPowReductionMulEquiv he X : GL ι (ZMod (p ^ (e + 1)))) :
        Matrix ι ι (ZMod (p ^ (e + 1))))
      = 1 + matrixMulPow ι p e X.toAdd := (rfl)

theorem nat_card_ker_glPowReduction [NeZero p] (he : 1 ≤ e) :
    Nat.card ((glPowReduction ι p e).ker) = p ^ (Fintype.card ι ^ 2) := by
  rw [← Nat.card_congr (kerGlPowReductionMulEquiv (ι := ι) (p := p) (e := e) he).toEquiv,
    ← Nat.card_congr (Multiplicative.ofAdd (α := Matrix ι ι (ZMod p)))]
  simp [Matrix, Nat.card_eq_fintype_card, pow_two, pow_mul]

theorem isMulCommutative_ker_glPowReduction [NeZero p] (he : 1 ≤ e) :
    IsMulCommutative ((glPowReduction ι p e).ker) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨X, rfl⟩ := (kerGlPowReductionMulEquiv (ι := ι) (p := p) (e := e) he).surjective a
  obtain ⟨Y, rfl⟩ := (kerGlPowReductionMulEquiv (ι := ι) (p := p) (e := e) he).surjective b
  rw [← map_mul, ← map_mul, mul_comm]

theorem exponent_ker_glPowReduction_dvd [NeZero p] (he : 1 ≤ e) :
    Monoid.exponent ((glPowReduction ι p e).ker) ∣ p := by
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro g
  obtain ⟨X, rfl⟩ := (kerGlPowReductionMulEquiv (ι := ι) (p := p) (e := e) he).surjective g
  rw [← map_pow]
  convert map_one (kerGlPowReductionMulEquiv (ι := ι) (p := p) (e := e) he) using 2
  refine Multiplicative.toAdd.injective ?_
  change p • X.toAdd = (0 : Matrix ι ι (ZMod p))
  ext i j
  simp

end CFSG.FeitThompson
