
module

public import CFSG.Certificates.Kernel.P0RankK.Conj
public import CFSG.Certificates.Kernel.P0RankK.Collector

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop CFSG.KC.P0Col
open scoped commutatorElement

theorem tVec_one_eq : tVec (1 : Dfull) = 0 := by
  rw [← pc_tD_zero, tVec_tD, bvec_zero]

theorem sCoord_lD {σ : ℕ} (hσ : σ < 2 ^ 16) :
    sCoord (⟨lD σ, lD_mem_Lgrp σ⟩ : Lgrp) = Multiplicative.ofAdd (bvec 16 σ) := by
  have hmem : lD σ * (1 : Dfull) ∈ Lgrp := by
    rw [mul_one]
    exact lD_mem_Lgrp σ
  have h := sCoord_lD_mul hσ T9.one_mem hmem
  rwa [show (⟨lD σ * 1, hmem⟩ : Lgrp) = ⟨lD σ, lD_mem_Lgrp σ⟩ from Subtype.ext (mul_one _)] at h

theorem qN_actK_eq_zero (κ : ℕ) {σ : ℕ} (hσ : σ < 2 ^ 16)
    (hq : MonsterB.P0Rank.qN p0Data.beta σ = 0) :
    MonsterB.P0Rank.qN p0Data.beta (actK p0Data.aCols κ σ) = 0 := by
  let X : Lgrp := ⟨lD σ, lD_mem_Lgrp σ⟩
  have hX : sCoord X = Multiplicative.ofAdd (bvec 16 σ) := sCoord_lD hσ
  have hX2T : (X : Dfull) ^ 2 ∈ T9 := by
    have h1 : sCoord (X ^ 2) = 1 := by
      rw [map_pow, hX, ← ofAdd_nsmul, two_nsmul]
      have : bvec 16 σ + bvec 16 σ = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero _
      rw [this, ofAdd_zero]
    have h2 := (sCoord_eq_one_iff (X ^ 2)).1 h1
    rwa [Subgroup.coe_pow] at h2
  have hX2 : (X : Dfull) ^ 2 = 1 := by
    apply eq_of_tVec_eq hX2T T9.one_mem
    rw [tVec_sq X, hX, toAdd_ofAdd, ← bvec_qN hσ, hq, bvec_zero, tVec_one_eq]
  let Y : Lgrp := ⟨uE κ * X * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) X.2⟩
  have hY : sCoord Y = Multiplicative.ofAdd (bvec 16 (actK p0Data.aCols κ σ)) :=
    sCoord_conj_uE_bvec κ X hσ hX
  have hY2 : (Y : Dfull) ^ 2 = 1 := by
    change (uE κ * (X : Dfull) * (uE κ)⁻¹) ^ 2 = 1
    rw [conj_pow, hX2, mul_one, mul_inv_cancel]
  have h := tVec_sq Y
  rw [hY2, hY, toAdd_ofAdd, ← bvec_qN (actK_aCols_lt κ hσ), tVec_one_eq, ← bvec_zero 9] at h
  exact bvec_inj (qN_lt _) (Nat.two_pow_pos 9) h.symm

theorem betaN_actK_eq_zero (κ : ℕ) {σ δ : ℕ} (hσ : σ < 2 ^ 16) (hδ : δ < 2 ^ 16)
    (hb : betaN p0Data.beta σ δ = 0) :
    betaN p0Data.beta (actK p0Data.aCols κ σ) (actK p0Data.aCols κ δ) = 0 := by
  let X : Lgrp := ⟨lD σ, lD_mem_Lgrp σ⟩
  let Z : Lgrp := ⟨lD δ, lD_mem_Lgrp δ⟩
  have hX : sCoord X = Multiplicative.ofAdd (bvec 16 σ) := sCoord_lD hσ
  have hZ : sCoord Z = Multiplicative.ofAdd (bvec 16 δ) := sCoord_lD hδ
  have hXZ : ⁅(X : Dfull), (Z : Dfull)⁆ = 1 := by
    apply eq_of_tVec_eq (commutator_mem_T9 X Z) T9.one_mem
    rw [tVec_commutator X Z, hX, hZ, toAdd_ofAdd, toAdd_ofAdd, ← bvec_betaN hσ hδ, hb,
      bvec_zero, tVec_one_eq]
  let Y : Lgrp := ⟨uE κ * X * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) X.2⟩
  let W : Lgrp := ⟨uE κ * Z * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) Z.2⟩
  have hY := sCoord_conj_uE_bvec κ X hσ hX
  have hW := sCoord_conj_uE_bvec κ Z hδ hZ
  have hYW : ⁅(Y : Dfull), (W : Dfull)⁆ = 1 := by
    have e : ⁅(Y : Dfull), (W : Dfull)⁆ = uE κ * ⁅(X : Dfull), (Z : Dfull)⁆ * (uE κ)⁻¹ := by
      change ⁅uE κ * (X : Dfull) * (uE κ)⁻¹, uE κ * (Z : Dfull) * (uE κ)⁻¹⁆ = _
      simp only [commutatorElement_def]
      group
    rw [e, hXZ, mul_one, mul_inv_cancel]
  have h := tVec_commutator Y W
  rw [hYW, tVec_one_eq] at h
  change 0 = lBeta (sCoord Y).toAdd (sCoord W).toAdd at h
  rw [hY, hW, toAdd_ofAdd, toAdd_ofAdd,
    ← bvec_betaN (actK_aCols_lt κ hσ) (actK_aCols_lt κ hδ), ← bvec_zero 9] at h
  exact bvec_inj (betaN_lt _ _) (Nat.two_pow_pos 9) h.symm

end CFSG.Monster.B.TwoA.Sp8.WordRel
