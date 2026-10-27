module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24Census
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi23 (fi23Gens fi23Hom fi23P
  fi23P_eq_closure_permsA fi23_conj_of_fix fixP_fi23Reps fi23Hom_injective fi23Reps)

@[expose] def fi23FourCheck (sp : String) (ix iz : ℕ) : Bool :=
  let prog := decodePairs sp
  let regs := slpRegs 31671 fi23Gens prog
  slpOK 31671 fi23Gens prog && decide (ix < regs.size) && decide (iz < regs.size) &&
    fixA 31671 regs[ix]! == 3511 &&
    eqA 31671 (compA 31671 regs[ix]! regs[ix]!) (idA 31671) &&
    commA 31671 regs[ix]! regs[iz]! &&
    eqA 31671 (powA 31671 regs[iz]! 4) (idA 31671) &&
    !eqA 31671 (powA 31671 regs[iz]! 2) (idA 31671)

theorem fixP_one : fixP (1 : Equiv.Perm (Fin 31671)) = 31671 := by
  rw [fixP]
  simp

theorem exists_orderOf_eq_four_of_check
    {sp : String} {ix iz : ℕ} (h : fi23FourCheck sp ix iz = true) :
    ∃ y : CFSG.Sporadic.Fi23.J, y * CFSG.Sporadic.Fi23.d = CFSG.Sporadic.Fi23.d * y ∧
      orderOf y = 4 := by
  simp only [fi23FourCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hslp, hix⟩, hiz⟩, hfix⟩, hx2⟩, hcomm⟩, hz4⟩, hz2⟩ := h
  obtain ⟨gx, hgx, hrx⟩ := rep_slpRegs hslp ix hix
  obtain ⟨gz, hgz, hrz⟩ := rep_slpRegs hslp iz hiz
  rw [← fi23P_eq_closure_permsA] at hgx hgz
  have hx2' : gx ^ 2 = 1 := by
    rw [sq]
    exact eq_of_eqA (rep_compA hrx hrx) rep_idA hx2
  have hfixx : fixP gx = 3511 := by rw [← fixA_eq hrx, hfix]
  have hx1 : gx ≠ 1 := fun h1 => by
    rw [h1, fixP_one] at hfixx
    exact absurd hfixx (by norm_num)
  have hc : gx * gz = gz * gx := (commA_iff hrx hrz).mp hcomm
  have hz4' : gz ^ 4 = 1 := eq_of_eqA (rep_powA hrz 4) rep_idA hz4
  have hz2' : gz ^ 2 ≠ 1 := fun he => by
    have := (eqA_iff (rep_powA hrz 2) rep_idA).mpr he
    rw [this] at hz2
    exact absurd hz2 (by decide)
  have hoz : orderOf gz = 4 := by
    have h1 : ¬ gz ^ 2 ^ 1 = 1 := by simpa using hz2'
    have h2 : gz ^ 2 ^ (1 + 1) = 1 := by simpa using hz4'
    simpa using orderOf_eq_prime_pow h1 h2
  have hd : fi23Hom CFSG.Sporadic.Fi23.d ∈ fi23P := ⟨_, rfl⟩
  have hd2 : (fi23Hom CFSG.Sporadic.Fi23.d) ^ 2 = 1 := by
    rw [← map_pow, ← CFSG.Sporadic.Fi23.orderOf_d, pow_orderOf_eq_one, map_one]
  have hd1 : fi23Hom CFSG.Sporadic.Fi23.d ≠ 1 := fun he => by
    have h1 := CFSG.Sporadic.Fi23.orderOf_d
    rw [fi23Hom_injective (he.trans (map_one fi23Hom).symm), orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hdfix : fixP (fi23Hom CFSG.Sporadic.Fi23.d) = 3511 := by
    have hf := fixP_fi23Reps
    simp only [fi23Reps, List.map_cons, List.map_nil, List.cons.injEq] at hf
    exact hf.1
  obtain ⟨w, hwP, hw⟩ := fi23_conj_of_fix hgx hx2' hx1 hd hd2 hd1 (by rw [hfixx, hdfix])
  have hz' : w * gz * w⁻¹ ∈ fi23P := fi23P.mul_mem (fi23P.mul_mem hwP hgz) (fi23P.inv_mem hwP)
  obtain ⟨y, hy⟩ := hz'
  refine ⟨y, fi23Hom_injective ?_, ?_⟩
  · rw [map_mul, map_mul, hy, ← hw]
    calc w * gz * w⁻¹ * (w * gx * w⁻¹) = w * (gz * gx) * w⁻¹ := by group
      _ = w * (gx * gz) * w⁻¹ := by rw [hc]
      _ = w * gx * w⁻¹ * (w * gz * w⁻¹) := by group
  · rw [← orderOf_injective fi23Hom fi23Hom_injective, hy, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hoz]

theorem transpositionOrderFour_of_check
    {sp : String} {ix iz : ℕ} (h : fi23FourCheck sp ix iz = true) :
    TranspositionOrderFour := by
  obtain ⟨y, -, hy⟩ := exists_orderOf_eq_four_of_check h
  refine ⟨((CFSG.Sporadic.Fi24.fi23EquivMR.symm (CFSG.Sporadic.Fi23.fi23EquivJ.symm y) :
    ↥CFSG.Sporadic.Fi24.MR) : CFSG.Sporadic.Fi24.R), Subtype.mem _, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hy]

theorem twoAOrderFour_of_check
    {sp : String} {ix iz : ℕ} (h : fi23FourCheck sp ix iz = true) :
    TwoAOrderFour := by
  obtain ⟨y, hyd, hy⟩ := exists_orderOf_eq_four_of_check h
  obtain ⟨c, hc⟩ := isConj_iff.mp CFSG.Sporadic.Fi24.sb_mem_D23
  refine ⟨CFSG.Sporadic.Fi24.fromFi23 (c * y * c⁻¹), ?_, ?_⟩
  · rw [CFSG.Sporadic.Fi24.LE_eq_map]
    refine ⟨c * y * c⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← hc]
    calc c * y * c⁻¹ * (c * CFSG.Sporadic.Fi23.d * c⁻¹) = c * (y * CFSG.Sporadic.Fi23.d) * c⁻¹ := by
          group
      _ = c * (CFSG.Sporadic.Fi23.d * y) * c⁻¹ := by rw [hyd]
      _ = c * CFSG.Sporadic.Fi23.d * c⁻¹ * (c * y * c⁻¹) := by group
  · rw [orderOf_injective _ CFSG.Sporadic.Fi24.fromFi23_injective, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hy]

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
