module

public import CFSG.ClassicalInvolution.Asc77.AscT7MA
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15

variable {p : ℕ} [Fact p.Prime] {e : ℕ}


theorem twinSqAlpha_psp2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) : TwinSqAlpha p e .PSp 2 := by
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have : Group.IsPerfect (modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 p e Fact.out trivial hadm).1.1
  refine twinSqAlphaOn_of_autSq (t := .PSp) (modelUniv .PSp 2 p e Fact.out)
    (proj 2 (GaloisField p e)) proj_surjective ?_ ?_ ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · exact fund_noncentral_modelUniv trivial hadm (by simp)
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    exact OuterSp4.psp4_autVac h2 h4
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

end CFSG.ClassicalInvolution.Asc77
