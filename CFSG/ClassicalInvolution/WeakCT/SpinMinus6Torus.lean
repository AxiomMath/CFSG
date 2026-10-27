module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Unipotent

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs

section Torus

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

variable (b c) in
@[expose] noncomputable def dT (s : Fˣ) : spinGroup (quadMinus 3 F b c) :=
  (minusFrame 3 b c).longTorus nodeZero_ne_nodeOne true false s

@[expose] noncomputable def sT (a : Fin 2 → F) : spinGroup (quadMinus 3 F b c) :=
  shortTorusElt 3 hirr finOne a

theorem longCoroot_qA : longCoroot nodeZero finOne true false nodeZero true +
    longCoroot nodeZero finOne true false finOne false = 2 := by decide

theorem longCoroot_qC : longCoroot nodeZero finOne true false nodeZero true +
    longCoroot nodeZero finOne true false finOne true = 0 := by decide

theorem longCoroot_qB : longCoroot nodeZero finOne true false nodeZero true = 1 := by decide

theorem longCoroot_nN : longCoroot nodeZero finOne true false finOne true = -1 := by decide

omit hirr in
theorem shortTorusScalar_zero (a : Fin 2 → F) (r : Bool) :
    shortTorusScalar 3 b c finOne a nodeZero r = 1 := by
  unfold shortTorusScalar
  rw [ite_eq_right_of_eq_false _ _ (eq_false nodeZero_ne_nodeOne)]

omit hirr in
theorem shortTorusScalar_one_true (a : Fin 2 → F) :
    shortTorusScalar 3 b c finOne a finOne true = planeNorm b c a := by
  unfold shortTorusScalar
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

omit hirr in
theorem shortTorusScalar_one_false (a : Fin 2 → F) :
    shortTorusScalar 3 b c finOne a finOne false = (planeNorm b c a)⁻¹ := by
  unfold shortTorusScalar
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

theorem dT_conj_qA (s : Fˣ) (x : F) :
    dT b c s * qA b c (.ofAdd x) * (dT b c s)⁻¹ = qA b c (.ofAdd ((s : F) ^ 2 * x)) := by
  have h := (minusFrame 3 b c).longTorus_conj_longRoot nodeZero_ne_nodeOne true false s
    nodeZero_ne_nodeOne true false x
  rw [dT, qA, h, longCoroot_qA]
  simp

theorem dT_conj_qC (s : Fˣ) (y : F) :
    dT b c s * qC b c (.ofAdd y) * (dT b c s)⁻¹ = qC b c (.ofAdd y) := by
  have h := (minusFrame 3 b c).longTorus_conj_longRoot nodeZero_ne_nodeOne true false s
    nodeZero_ne_nodeOne true true y
  rw [dT, qC, h, longCoroot_qC]
  simp

theorem dT_conj_qB (s : Fˣ) (w : Fin 2 → F) :
    dT b c s * qB hirr (.ofAdd w) * (dT b c s)⁻¹ = qB hirr (.ofAdd ((s : F) • w)) := by
  have h := longTorus_conj_twShortRoot 3 hirr nodeZero_ne_nodeOne true false s nodeZero true w
  rw [dT, qB, h, longCoroot_qB]
  simp

theorem dT_conj_nN (s : Fˣ) (w : Fin 2 → F) :
    dT b c s * nN hirr (.ofAdd w) * (dT b c s)⁻¹ = nN hirr (.ofAdd (((s⁻¹ : Fˣ) : F) • w)) := by
  have h := longTorus_conj_twShortRoot 3 hirr nodeZero_ne_nodeOne true false s finOne true w
  rw [dT, nN, h, longCoroot_nN]
  simp

theorem sT_conj_qA {a : Fin 2 → F} (ha : a ≠ 0) (x : F) :
    sT hirr a * qA b c (.ofAdd x) * (sT hirr a)⁻¹ =
      qA b c (.ofAdd ((planeNorm b c a)⁻¹ * x)) := by
  have h := shortTorusElt_conj_longRoot 3 hirr finOne ha nodeZero_ne_nodeOne true false x
  rw [sT, qA, h, shortTorusScalar_zero, shortTorusScalar_one_false, one_mul]

theorem sT_conj_qC {a : Fin 2 → F} (ha : a ≠ 0) (y : F) :
    sT hirr a * qC b c (.ofAdd y) * (sT hirr a)⁻¹ = qC b c (.ofAdd (planeNorm b c a * y)) := by
  have h := shortTorusElt_conj_longRoot 3 hirr finOne ha nodeZero_ne_nodeOne true true y
  rw [sT, qC, h, shortTorusScalar_zero, shortTorusScalar_one_true, one_mul]

theorem sT_conj_qB {a : Fin 2 → F} (ha : a ≠ 0) (w : Fin 2 → F) :
    sT hirr a * qB hirr (.ofAdd w) * (sT hirr a)⁻¹ =
      qB hirr (.ofAdd (planeRefl b c a (planeRefl b c planeOne w))) :=
  shortTorusElt_conj_shortPosHom_of_ne 3 hirr nodeZero_ne_nodeOne ha w

theorem sT_conj_nN {a : Fin 2 → F} (ha : a ≠ 0) (w : Fin 2 → F) :
    sT hirr a * nN hirr (.ofAdd w) * (sT hirr a)⁻¹ =
      nN hirr (.ofAdd (planeNorm b c a • planeRefl b c a (planeRefl b c planeOne w))) :=
  shortTorusElt_conj_shortPosHom 3 hirr finOne ha w

omit hirr in
theorem planeRefl_smul_planeOne {t : F} (ht : t ≠ 0) (p : Fin 2 → F) :
    planeRefl b c (t • planeOne) p = planeRefl b c planeOne p := by
  unfold planeRefl
  rw [polarPlane_smul_right, planeNorm_smul, planeNorm_planeOne, smul_smul]
  congr 2
  field_simp

theorem smul_planeOne_ne_zero {t : F} (ht : t ≠ 0) : (t • planeOne : Fin 2 → F) ≠ 0 :=
  smul_ne_zero ht planeOne_ne_zero

omit hirr in
theorem planeNorm_smul_planeOne (t : F) : planeNorm b c (t • planeOne : Fin 2 → F) = t ^ 2 := by
  rw [planeNorm_smul, planeNorm_planeOne, mul_one]

theorem sT_smul_conj_qA {t : F} (ht : t ≠ 0) (x : F) :
    sT hirr (t • planeOne) * qA b c (.ofAdd x) * (sT hirr (t • planeOne))⁻¹ =
      qA b c (.ofAdd ((t ^ 2)⁻¹ * x)) := by
  rw [sT_conj_qA hirr (smul_planeOne_ne_zero ht), planeNorm_smul_planeOne]

theorem sT_smul_conj_qC {t : F} (ht : t ≠ 0) (y : F) :
    sT hirr (t • planeOne) * qC b c (.ofAdd y) * (sT hirr (t • planeOne))⁻¹ =
      qC b c (.ofAdd (t ^ 2 * y)) := by
  rw [sT_conj_qC hirr (smul_planeOne_ne_zero ht), planeNorm_smul_planeOne]

theorem sT_smul_conj_qB {t : F} (ht : t ≠ 0) (w : Fin 2 → F) :
    sT hirr (t • planeOne) * qB hirr (.ofAdd w) * (sT hirr (t • planeOne))⁻¹ =
      qB hirr (.ofAdd w) := by
  rw [sT_conj_qB hirr (smul_planeOne_ne_zero ht), planeRefl_smul_planeOne ht,
    planeRefl_planeRefl planeNorm_planeOne_ne_zero]

theorem sT_smul_conj_nN {t : F} (ht : t ≠ 0) (w : Fin 2 → F) :
    sT hirr (t • planeOne) * nN hirr (.ofAdd w) * (sT hirr (t • planeOne))⁻¹ =
      nN hirr (.ofAdd (t ^ 2 • w)) := by
  rw [sT_conj_nN hirr (smul_planeOne_ne_zero ht), planeRefl_smul_planeOne ht,
    planeRefl_planeRefl planeNorm_planeOne_ne_zero, planeNorm_smul_planeOne]

@[expose] noncomputable def zT (t : Fˣ) : spinGroup (quadMinus 3 F b c) :=
  dT b c (t ^ 2) * sT hirr ((t : F) • planeOne)

theorem zT_conj_qA (t : Fˣ) (x : F) :
    zT hirr t * qA b c (.ofAdd x) * (zT hirr t)⁻¹ = qA b c (.ofAdd ((t : F) ^ 2 * x)) := by
  have e : zT hirr t * qA b c (.ofAdd x) * (zT hirr t)⁻¹ =
      dT b c (t ^ 2) * (sT hirr ((t : F) • planeOne) * qA b c (.ofAdd x) *
        (sT hirr ((t : F) • planeOne))⁻¹) * (dT b c (t ^ 2))⁻¹ := by
    rw [zT]
    group
  rw [e, sT_smul_conj_qA hirr t.ne_zero, dT_conj_qA]
  congr 2
  have := t.ne_zero
  push_cast
  field_simp

theorem zT_conj_qC (t : Fˣ) (y : F) :
    zT hirr t * qC b c (.ofAdd y) * (zT hirr t)⁻¹ = qC b c (.ofAdd ((t : F) ^ 2 * y)) := by
  have e : zT hirr t * qC b c (.ofAdd y) * (zT hirr t)⁻¹ =
      dT b c (t ^ 2) * (sT hirr ((t : F) • planeOne) * qC b c (.ofAdd y) *
        (sT hirr ((t : F) • planeOne))⁻¹) * (dT b c (t ^ 2))⁻¹ := by
    rw [zT]
    group
  rw [e, sT_smul_conj_qC hirr t.ne_zero, dT_conj_qC]

theorem zT_conj_qB (t : Fˣ) (w : Fin 2 → F) :
    zT hirr t * qB hirr (.ofAdd w) * (zT hirr t)⁻¹ = qB hirr (.ofAdd ((t : F) ^ 2 • w)) := by
  have e : zT hirr t * qB hirr (.ofAdd w) * (zT hirr t)⁻¹ =
      dT b c (t ^ 2) * (sT hirr ((t : F) • planeOne) * qB hirr (.ofAdd w) *
        (sT hirr ((t : F) • planeOne))⁻¹) * (dT b c (t ^ 2))⁻¹ := by
    rw [zT]
    group
  rw [e, sT_smul_conj_qB hirr t.ne_zero, dT_conj_qB]
  simp

theorem zT_conj_nN (t : Fˣ) (w : Fin 2 → F) :
    zT hirr t * nN hirr (.ofAdd w) * (zT hirr t)⁻¹ = nN hirr (.ofAdd w) := by
  have e : zT hirr t * nN hirr (.ofAdd w) * (zT hirr t)⁻¹ =
      dT b c (t ^ 2) * (sT hirr ((t : F) • planeOne) * nN hirr (.ofAdd w) *
        (sT hirr ((t : F) • planeOne))⁻¹) * (dT b c (t ^ 2))⁻¹ := by
    rw [zT]
    group
  rw [e, sT_smul_conj_nN hirr t.ne_zero, dT_conj_nN, smul_smul]
  have h1 : (((t ^ 2)⁻¹ : Fˣ) : F) * (t : F) ^ 2 = 1 := by
    have := t.ne_zero
    push_cast
    field_simp
  rw [h1, one_smul]

end Torus

end CFSG.ClassicalInvolution.WeakCT
