module

public import CFSG.Certificates.Kernel.SporSch.Co1RankRepSound
public import CFSG.Sporadic.Co1Block.TwoCCent

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankTab CFSG.KC.Co1B CFSG.KC.Co1Cl
  CFSG.KC.Co1RankBnd CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem rank_conj_sub_one {n K : Type*} [Fintype n] [DecidableEq n] [Field K] (g x : GL n K) :
    (((g * x * g⁻¹ : GL n K) : Matrix n n K) - 1).rank = ((x : Matrix n n K) - 1).rank := by
  have e : ((g * x * g⁻¹ : GL n K) : Matrix n n K) - 1 =
      (g : Matrix n n K) * ((x : Matrix n n K) - 1) * ((g⁻¹ : GL n K) : Matrix n n K) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _)]

theorem rankRC_sound (X : ℕ) :
    rankRC 24 24 (Nat.xor X oneK) = (matK X - 1 : Matrix (Fin 24) (Fin 24) (ZMod 2)).rank := by
  have hrow : ∀ (Y : ℕ) (t j : Fin 24), matK Y t j = if Y.testBit (24 * t + j) then 1 else 0 := by
    intro Y t j
    simp only [matK, CFSG.Sporadic.SmallF2.rowsMatrix_apply, CFSG.KC.Co1F2.unpackR,
      Array.getElem?_ofFn, t.isLt, ↓reduceDIte, Option.getD_some,
      CFSG.Sporadic.SmallF2.toVecD_apply, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, j.isLt,
      decide_true, Bool.true_and]
    rw [add_comm]
  rw [CFSG.KS.SporSch.Co1RankRC.rankRC_eq_rank]
  congr 1
  ext t j
  rw [Matrix.sub_apply, ← matK_oneK, hrow, hrow, Matrix.of_apply, CFSG.KS.SporSch.Co1RankRC.rowV]
  have e : (Nat.xor X oneK).testBit (24 * t + j) =
      (X.testBit (24 * t + j) ^^ oneK.testBit (24 * t + j)) := Nat.testBit_xor X oneK _
  rw [e]
  cases X.testBit (24 * t + j) <;> cases oneK.testBit (24 * t + j) <;> decide

theorem ncard_fix_of_rank
    (hA₁ : ((A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    (hcG : ((cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    {z : GL24} (hz : z ∈ GA) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hr : ((z : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank = 8) : (xFix z).ncard = 2280 := by
  have ho : orderOf (⟨z, hz⟩ : GA) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hconj : ∀ y : GA, IsConj (⟨z, hz⟩ : GA) y →
      (((y : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank = 8 := by
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    have e : ((c : GA) : GL24) * z * ((c : GA) : GL24)⁻¹ = (y : GL24) := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [← e, rank_conj_sub_one]
    exact hr
  rcases involution_classes.1 _ ho with h | h | h
  · have := ncard_fix_isConj h
    rw [ncard_fix_aC] at this
    exact this.symm
  · exact absurd (hconj _ h) hcG
  · exact absurd (hconj _ h) (by rw [coe_a₁]; exact hA₁)

theorem lor_split (z d : ℕ) :
    Nat.lor (Nat.shiftLeft (z >>> d) d) (Nat.land z (Co1RankCoord.mask d)) = z := by
  have hlo := land_mask_lt z d
  change ((z >>> d) <<< d) ||| Nat.land z (Co1RankCoord.mask d) = z
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, land_mask]
  exact Nat.div_add_mod' z (2 ^ d)

theorem matK_eltM {D : Co1RankTab.Dat} {gens : ℕ → GL24} (hM : chkM D = true)
    (htab : tabOK D = true)
    (hG : ∀ g < D.nG, matK (getM D.G g) = (gens g : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    {z : ℕ} (hz : z < 2 ^ (D.d + 7)) :
    ((el D.d (bU D) (wU D gens) z : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matK (eltM D z) := by
  obtain ⟨-, hsq, -, hWL, -, -, -, -⟩ := chkM_sound hM
  obtain ⟨hword, -⟩ := tabOK_sound htab
  have hsqM : ∀ s < D.d, matK (getM D.BS s) * matK (getM D.BS s) = 1 := fun s hs => by
    rw [← matK_mulWK, hsq s hs, matK_oneK]
  have hq : ∀ v, ((qProd (bU D) D.d v : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      matK (qOf D v) := fun v => by
    have e := qProd_map (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) (bU D) D.d v
    simp only [Units.coeHom_apply] at e
    rw [e, matK_qOf']
    exact qProd_congr_fun _ (fun s hs => val_bU (hsqM s hs)) v
  have hw : ∀ i < 128, ((wU D gens i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      matK (getM D.WL i) := fun i hi => by
    have e := wordP_map (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) gens 8 (getL D.CW i)
    simp only [Units.coeHom_apply] at e
    rw [hWL i hi, matK_walkM', matK_oneK, one_mul, wU, e]
    exact wordP_congr (fun g hg => (hG g hg).symm) 8 _ (hword i hi)
  rw [el, Units.val_mul, eltM, matK_mulWK, hw _ (shiftRight_lt hz), ← hq, land_mask, qProd_mod]
  rfl

theorem twoA_of_checks
    (hA₁ : ((A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    (hcG : ((cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    {D : Co1RankTab.Dat} {gens : ℕ → GL24} (hM : chkM D = true) (htab : tabOK D = true)
    (hG : ∀ g < D.nG, matK (getM D.G g) = (gens g : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    {z : ℕ} (hz : z < 2 ^ (D.d + 7)) (hzA : Co1RankCand.in2A (candT D) z = true)
    (hGA : el D.d (bU D) (wU D gens) z ∈ GA)
    (hzz : el D.d (bU D) (wU D gens) z * el D.d (bU D) (wU D gens) z = 1)
    (hz1 : el D.d (bU D) (wU D gens) z ≠ 1) :
    (xFix (el D.d (bU D) (wU D gens) z)).ncard = 2280 := by
  obtain ⟨-, -, -, -, -, -, -, h2A⟩ := chkM_sound hM
  have hbit : fld(getL (Co1RankCand.getLL D.T2A (Nat.shiftRight (Nat.shiftRight z D.d) 3))
      (Nat.land (Nat.shiftRight z D.d) 7), Nat.land z (Co1RankCoord.mask D.d), 1) = 1 := by
    have e : Co1RankCand.in2A (candT D) z = Nat.beq (fld(getL (Co1RankCand.getLL D.T2A
        (Nat.shiftRight (Nat.shiftRight z D.d) 3)) (Nat.land (Nat.shiftRight z D.d) 7),
        Nat.land z (Co1RankCoord.mask D.d), 1)) 1 := strictB_eq' _ _
    exact Nat.eq_of_beq_eq_true (e ▸ hzA)
  have hr := h2A _ (shiftRight_lt hz) _ (land_mask_lt z D.d) hbit
  rw [lor_split, rankRC_sound, ← matK_eltM hM htab hG hz] at hr
  exact ncard_fix_of_rank hA₁ hcG hGA hzz hz1 hr

end CFSG.KS.SporSch.Co1Rank

end
