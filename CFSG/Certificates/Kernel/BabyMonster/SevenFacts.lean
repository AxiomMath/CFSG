module

public import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenLocal.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SevenLocal.Data1
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic
public import CFSG.Certificates.Kernel.BSeed.Sound

public section

namespace CFSG.KC.BM.SevenFacts

open CFSG.KC.BM

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def Fact17101Of (Al X Y T1 T2 E : MatB) : Prop :=
  Al * Al = 1 ∧ Al ≠ 1 ∧ (Al - 1).rank = 1860 ∧ Al * X = X * Al ∧ Al * Y = Y * Al ∧
    X ^ 7 = 1 ∧ X ≠ 1 ∧ Y ^ 5 = 1 ∧ Y ≠ 1 ∧ X * Y = Y * X ∧
    T1 * T1 = 1 ∧ (T1 - 1).rank = 1860 ∧ T1 * X = X * T1 ∧ T1 * Al = Al * T1 ∧ T1 ≠ Al ∧
    T2 * T2 = 1 ∧ (T2 - 1).rank = 1860 ∧ T2 * X = X * T2 ∧ T1 * T2 = T2 * T1 ∧ T1 ≠ T2 ∧
    (T1 * T2 - 1).rank = 2048 ∧ E ^ 3 = 1 ∧ E ≠ 1 ∧ E * X = X * E ∧ E * T1 = T1 * E ∧
    E * Al = Al * E ∧ (T1 * E) ^ 6 = 1 ∧ (T1 * E) ^ 2 ≠ 1 ∧ (T1 * E) ^ 3 = T1 ∧
    T1 * Y * T1 * Y ^ 4 ≠ 1 ∧ T1 * Y * T1 * Y ^ 4 ≠ Al

@[expose] def w3W (Y T1 T2 E : MatB) : MatB :=
  E ^ 2 * Y * E * Y ^ 4 * T2 * Y ^ 4 * E ^ 2 * T1 * Y * T1 * Y

@[expose] def w4W (Y T2 E : MatB) : MatB := E ^ 2 * Y ^ 4 * E ^ 2 * T2 * Y * E

@[expose] def fW (Y T1 T2 E : MatB) : MatB := Y * T1 * Y * E ^ 2 * T2 * Y * E ^ 2 * Y * Y * E

@[expose] def v1W (Y E : MatB) : MatB := Y ^ 4 * E * Y ^ 4 * E * Y * E * Y * E

@[expose] def v2W (Y T1 T2 E : MatB) : MatB := Y * E * Y ^ 4 * T2 * Y * Y * E ^ 2 * T1 * Y

@[expose] def Fact17450Of (Al X T1 S3 S4 F U1 U2 : MatB) : Prop :=
  (Al * X - 1).rank = 3996 ∧ (Al * T1 - 1).rank = 2158 ∧ (T1 * X - 1).rank = 4008 ∧
    S3 * S3 = 1 ∧ (S3 - 1).rank = 1860 ∧ S3 * X = X * S3 ∧ (T1 * S3) ^ 3 = 1 ∧ T1 * S3 ≠ 1 ∧
    S4 * S4 = 1 ∧ (S4 - 1).rank = 1860 ∧ S4 * X = X * S4 ∧ (T1 * S4) ^ 4 = 1 ∧
    (T1 * S4) ^ 2 ≠ 1 ∧ ((T1 * S4) ^ 2 - 1).rank = 2048 ∧
    F ^ 7 = 1 ∧ F ≠ 1 ∧ F * X = X * F ∧ F * Al = Al * F ∧ F * T1 = T1 * F ∧
    (∀ i < 7, F ≠ X ^ i) ∧
    (Al * F - 1).rank = 4008 ∧ (T1 * (X * F) - 1).rank = 4008 ∧
    (T1 * (X * F ^ 2) - 1).rank = 4008 ∧ (Al * (X * F ^ 3) - 1).rank = 4008 ∧
    (T1 * (X * F ^ 4) - 1).rank = 4008 ∧ (Al * (X * F ^ 5) - 1).rank = 4008 ∧
    (Al * (X * F ^ 6) - 1).rank = 4008 ∧
    U1 ^ 3 = 1 ∧ U1 ≠ 1 ∧ U2 ^ 3 = 1 ∧ U2 ≠ 1 ∧ U1 * X = X * U1 ∧ U2 * X = X * U2 ∧
    U1 * U2 = U2 * U1 ∧ (∀ i < 3, U2 ≠ U1 ^ i) ∧
    (U1 - 1).rank = 2862 ∧ (U2 - 1).rank = 2862 ∧ (U1 * U2 - 1).rank = 2862 ∧
    (U1 * (U2 * U2) - 1).rank = 2862

@[expose] def SevenWords : Prop :=
  stripMat Seven.al = stripMat Seven.m2 ^ 19 ∧ stripMat Seven.x = stripMat Seven.g ^ 10 ∧
    stripMat Seven.y = stripMat Seven.g ^ 14 ∧
    stripMat Seven.t2 = stripMat Seven.y ^ 3 * stripMat Seven.t1 * stripMat Seven.y ^ 2

@[expose] def Fact17101 : Prop :=
  SevenWords ∧ Fact17101Of (stripMat Seven.al) (stripMat Seven.x) (stripMat Seven.y)
    (stripMat Seven.t1) (stripMat Seven.t2) (stripMat Seven.e3)

@[expose] def Fact17599 : Prop :=
  stripMat Seven.y = stripMat Seven.g ^ 14 ∧ (stripMat Seven.y - 1).rank = 3480

@[expose] def Fact17450 : Prop :=
  SevenWords ∧
    stripMat SevenLocal.s3 = w3W (stripMat Seven.y) (stripMat Seven.t1) (stripMat Seven.t2)
      (stripMat Seven.e3) ^ 7 ∧
    stripMat SevenLocal.s4 = w4W (stripMat Seven.y) (stripMat Seven.t2) (stripMat Seven.e3) ^ 7 ∧
    stripMat SevenLocal.f = fW (stripMat Seven.y) (stripMat Seven.t1) (stripMat Seven.t2)
      (stripMat Seven.e3) ∧
    stripMat SevenLocal.u1 = v1W (stripMat Seven.y) (stripMat Seven.e3) ^ 7 ∧
    stripMat SevenLocal.u2 = v2W (stripMat Seven.y) (stripMat Seven.t1) (stripMat Seven.t2)
      (stripMat Seven.e3) ^ 7 ∧
    Fact17450Of (stripMat Seven.al) (stripMat Seven.x) (stripMat Seven.t1) (stripMat SevenLocal.s3)
      (stripMat SevenLocal.s4) (stripMat SevenLocal.f) (stripMat SevenLocal.u1)
      (stripMat SevenLocal.u2)

end CFSG.KC.BM.SevenFacts

end
