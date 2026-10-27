module

public import CFSG.Certificates.Kernel.S1277KModSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Grp

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct

theorem bitV_xor (u v i x : ℕ) : bitV (u ^^^ v) i x = bitV u i x ^^^ bitV v i x := by
  unfold bitV
  rw [Nat.testBit_xor]
  cases u.testBit i <;> cases v.testBit i <;> simp

theorem app_xor (B : B6) (u v : ℕ) : B.app (u ^^^ v) = B.app u ^^^ B.app v := by
  simp only [B6.app, bitV_xor]
  ac_rfl

theorem app_zero (B : B6) : B.app 0 = 0 := by
  simp [B6.app, bitV]

theorem app_bitV (B : B6) (v i x : ℕ) : B.app (bitV v i x) = bitV v i (B.app x) := by
  unfold bitV
  cases v.testBit i <;> simp [app_zero]

theorem comp_app (B C : B6) (v : ℕ) : (B.comp C).app v = B.app (C.app v) := by
  rw [B6.app.eq_1 C v, app_xor, app_xor, app_xor, app_xor, app_xor, app_bitV, app_bitV, app_bitV,
    app_bitV, app_bitV, app_bitV, B6.app.eq_1 (B.comp C) v]
  rfl

theorem comp_assoc (B C D : B6) : (B.comp C).comp D = B.comp (C.comp D) := by
  rw [B6.comp.eq_1 (B.comp C) D]
  simp only [comp_app]
  rfl

theorem bitV_lt (v i x : ℕ) (hx : x < 64) : bitV v i x < 2 ^ 6 := by
  unfold bitV
  split_ifs
  · exact hx
  · norm_num

theorem app_lt (B : B6) (hB : B.Valid) (v : ℕ) : B.app v < 64 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hB
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (bitV_lt v 0 _ h0) (bitV_lt v 1 _ h1)) (bitV_lt v 2 _ h2))
    (bitV_lt v 3 _ h3)) (bitV_lt v 4 _ h4)) (bitV_lt v 5 _ h5)

section Tab

variable {G0 : List B6}

theorem getD_mem {i : ℕ} (hi : i < G0.length) : G0.getD i B6.id ∈ G0 := by
  rw [CFSG.KS.S1277Mod.getD_eq_get _ hi]
  exact List.getElem_mem hi

theorem getD_idxOf {X : B6} (hX : X ∈ G0) : G0.getD (G0.idxOf X) B6.id = X := by
  have h := List.idxOf_lt_length_iff.2 hX
  rw [CFSG.KS.S1277Mod.getD_eq_get _ h, List.getElem_idxOf h]

theorem appA_getD {n : ℕ} (hn : n < G0.length * 64) :
    (mkTab G0).appA.getD n 0 = (G0.getD (n / 64) B6.id).app (n % 64) := by
  change ((List.range (G0.length * 64)).map _).toArray.getD n 0 = _
  rw [CFSG.KS.S1277Mod.getD_range_map, if_pos hn]

theorem compA_getD {n : ℕ} (hn : n < G0.length * G0.length) :
    (mkTab G0).compA.getD n 0 =
      G0.idxOf ((G0.getD (n / G0.length) B6.id).comp (G0.getD (n % G0.length) B6.id)) := by
  change ((List.range (G0.length * G0.length)).map _).toArray.getD n 0 = _
  rw [CFSG.KS.S1277Mod.getD_range_map, if_pos hn]

theorem mulN_eq {x y : ℕ} (hx : x < G0.length * 64) (hy : y < G0.length * 64) :
    mulN (mkTab G0) x y =
      G0.idxOf ((G0.getD (x / 64) B6.id).comp (G0.getD (y / 64) B6.id)) * 64 +
        (x % 64 ^^^ (G0.getD (x / 64) B6.id).app (y % 64)) := by
  have hi : x / 64 < G0.length := by omega
  have hj : y / 64 < G0.length := by omega
  have hpos : 0 < G0.length := by omega
  have h1 : x / 64 * G0.length + y / 64 < G0.length * G0.length := by
    have : x / 64 * G0.length + y / 64 < (x / 64 + 1) * G0.length := by
      rw [Nat.add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hi)
  have h2 : x / 64 * 64 + y % 64 < G0.length * 64 := by omega
  have hnb : (mkTab G0).nb = G0.length := rfl
  rw [mulN, hnb, compA_getD h1, appA_getD h2]
  have e1 : (x / 64 * G0.length + y / 64) / G0.length = x / 64 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (x / 64 * G0.length + y / 64) % G0.length = y / 64 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have e3 : (x / 64 * 64 + y % 64) / 64 = x / 64 := by omega
  have e4 : (x / 64 * 64 + y % 64) % 64 = y % 64 := by omega
  rw [e1, e2, e3, e4]

variable (hval : ∀ B ∈ G0, B.Valid) (hcl : ∀ B ∈ G0, ∀ C ∈ G0, B.comp C ∈ G0)
include hval hcl

theorem mulN_lt {x y : ℕ} (hx : x < G0.length * 64) (hy : y < G0.length * 64) :
    mulN (mkTab G0) x y < G0.length * 64 := by
  have hi : x / 64 < G0.length := by omega
  have hj : y / 64 < G0.length := by omega
  rw [mulN_eq hx hy]
  have hk := List.idxOf_lt_length_iff.2 (hcl _ (getD_mem hi) _ (getD_mem hj))
  have hxor : x % 64 ^^^ (G0.getD (x / 64) B6.id).app (y % 64) < 64 :=
    Nat.xor_lt_two_pow (n := 6) (by omega) (app_lt _ (hval _ (getD_mem hi)) _)
  exact lt_of_lt_of_le (Nat.add_lt_add_left hxor _)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right 64 hk)

theorem div_mulN {x y : ℕ} (hx : x < G0.length * 64) (hy : y < G0.length * 64) :
    G0.getD (mulN (mkTab G0) x y / 64) B6.id =
      (G0.getD (x / 64) B6.id).comp (G0.getD (y / 64) B6.id) ∧
    mulN (mkTab G0) x y % 64 = x % 64 ^^^ (G0.getD (x / 64) B6.id).app (y % 64) := by
  have hi : x / 64 < G0.length := by omega
  have hj : y / 64 < G0.length := by omega
  have hxor : x % 64 ^^^ (G0.getD (x / 64) B6.id).app (y % 64) < 64 :=
    Nat.xor_lt_two_pow (n := 6) (by omega) (app_lt _ (hval _ (getD_mem hi)) _)
  have hX := hcl _ (getD_mem hi) _ (getD_mem hj)
  rw [mulN_eq hx hy]
  set t := x % 64 ^^^ (G0.getD (x / 64) B6.id).app (y % 64) with htdef
  set k := G0.idxOf ((G0.getD (x / 64) B6.id).comp (G0.getD (y / 64) B6.id)) with hkdef
  have hd : (k * 64 + t) / 64 = k := by omega
  have hm : (k * 64 + t) % 64 = t := by omega
  rw [hd, hm, hkdef, getD_idxOf hX]
  exact ⟨rfl, rfl⟩

theorem mulN_assoc {x y z : ℕ} (hx : x < G0.length * 64) (hy : y < G0.length * 64)
    (hz : z < G0.length * 64) :
    mulN (mkTab G0) (mulN (mkTab G0) x y) z = mulN (mkTab G0) x (mulN (mkTab G0) y z) := by
  have hxy := mulN_lt hval hcl hx hy
  have hyz := mulN_lt hval hcl hy hz
  rw [mulN_eq hxy hz, mulN_eq hx hyz, (div_mulN hval hcl hx hy).1, (div_mulN hval hcl hx hy).2,
    (div_mulN hval hcl hy hz).1, (div_mulN hval hcl hy hz).2, comp_assoc, app_xor, comp_app,
    Nat.xor_assoc]

end Tab

end CFSG.KS.S1277Grp

end
