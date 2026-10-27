module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public import CFSG.Monster.B.Pinned.Primes.FiveRelations
public import CFSG.Monster.B.Intertwiner.PairFacts
public import CFSG.Monster.Existence.BabyW2Classes
public import Certificates.Certificate13610

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.Blueprint

@[expose] noncomputable def tFive : NativeSporadic.B := hFive ^ 4

@[expose] noncomputable def cOneFive : NativeSporadic.B :=
  hFive⁻¹ * xFive * hFive

@[expose] noncomputable def cTwoFive : NativeSporadic.B :=
  (hFive ^ 3)⁻¹ * xFive * hFive ^ 3

@[expose] noncomputable def uFive : NativeSporadic.B :=
  (cOneFive * tFive * cOneFive⁻¹) * (cTwoFive * tFive * cTwoFive⁻¹) * (xFive * tFive * xFive⁻¹) *
    tFive

section Parts

theorem bFiveTwoB_parts : Matrix.rank (bMat tFive - 1) = 2048 ∧ uFive * uFive = 1 ∧
    uFive ≠ 1 ∧ Matrix.rank (bMat uFive - 1) = 2048 := by
  have hX : ((runG fiveProg glA₁ glA₂ 1 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat xFive := by
    rw [← bSeedGL_runG, coe_bSeedGL]
    rfl
  have hH : ((runG fiveProg glA₁ glA₂ 2 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat hFive := by
    rw [← bSeedGL_runG, coe_bSeedGL]
    rfl
  have h := Certificates.certificate13610
  rw [hX, hH] at h
  obtain ⟨hrt, huu, hu1, hru⟩ := h
  obtain ⟨hx5, -, hh8, -⟩ := five_facts
  have e7 : hFive ^ 7 = hFive⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hh8
  have e5 : hFive ^ 5 = (hFive ^ 3)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_add]
    exact hh8
  have e4 : xFive ^ 4 = xFive⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx5
  have hu : uFive = (hFive ^ 7 * xFive * hFive) * hFive ^ 4 * (hFive ^ 7 * xFive ^ 4 * hFive) *
      ((hFive ^ 5 * xFive * hFive ^ 3) * hFive ^ 4 * (hFive ^ 5 * xFive ^ 4 * hFive ^ 3)) *
      (xFive * hFive ^ 4 * xFive ^ 4) * hFive ^ 4 := by
    rw [uFive, cOneFive, cTwoFive, tFive, e7, e5, e4]
    group
  have hU : bMat uFive = CFSG.KC.BM.FiveA.uWord (bMat xFive) (bMat hFive) := by
    rw [hu, CFSG.KC.BM.FiveA.uWord]
    simp only [map_mul, map_pow]
  refine ⟨by rw [tFive, map_pow]; exact hrt,
    bMat_injective (by rw [map_mul, hU, map_one]; exact huu),
    fun h1 => hu1 (by rw [← hU, h1, map_one]), by rw [hU]; exact hru⟩

theorem orderOf_tFive : orderOf tFive = 2 := by
  obtain ⟨-, -, hh8, hh4, -⟩ := five_facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ hh4
  rw [tFive, ← pow_mul]
  exact hh8

theorem orderOf_uFive : orderOf uFive = 2 := by
  obtain ⟨-, huu, hu1, -⟩ := bFiveTwoB_parts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact huu) hu1

end Parts

section TwoB

theorem babyInv_one_tFive : CFSG.Monster.GMS.BabyInv 1 tFive :=
  CFSG.Monster.Existence.babyInv_one_of_rank_2048 orderOf_tFive bFiveTwoB_parts.1

theorem babyInv_one_uFive : CFSG.Monster.GMS.BabyInv 1 uFive :=
  CFSG.Monster.Existence.babyInv_one_of_rank_2048 orderOf_uFive bFiveTwoB_parts.2.2.2

end TwoB

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
