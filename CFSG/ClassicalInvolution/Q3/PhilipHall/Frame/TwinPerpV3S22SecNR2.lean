module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecNR1
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutSp
public import CFSG.ClassicalInvolution.Asc77.AscT7MD
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts (modelClauseZero)
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped MatrixGroups


section Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4

theorem sqNoRootC_psp2 : SqNoRootC (CompData.model .PSp 2) := by
  have hadm : StatedLieAdmissible .PSp 2 3 1 := Q3Z.statedLieAdmissible_psp2
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Nat.prime_three).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadm).1.1
  refine sqNoRootC_of_autSq (CompData.model .PSp 2) (proj 2 (GaloisField 3 1))
    proj_surjective ?_ (Q3TLK.fundNoncentral_model3 trivial hadm (by simp)) ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro R R' hR hR' hne x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' _
    exact Q3TIY.psp4_autVac3 Q3W.card_gf3 h2
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ'

end Sp

section SL

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem sqNoRootC_psl4 (hadm : StatedLieAdmissible .PSL 4 3 1) :
    SqNoRootC (CompData.model .PSL 4) := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hnsq : ¬ IsSquare (-1 : GaloisField 3 1) :=
    Asc77.not_isSquare_neg_one_galoisField (p := 3) (e := 1) (by norm_num) one_ne_zero
  have : Group.IsPerfect (modelUniv .PSL 4 3 1 Nat.prime_three).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 4 3 1 Nat.prime_three trivial hadm).1.1
  have hπk : (proj 4 (GaloisField 3 1)).ker = Subgroup.center SL(4, GaloisField 3 1) :=
    (ker_proj (n := 4) (K := GaloisField 3 1)).trans (scalars_eq_center 4 (GaloisField 3 1))
  refine sqNoRootC_of_autSq (CompData.model .PSL 4) (proj 4 (GaloisField 3 1))
    (proj_surjective 4 (GaloisField 3 1)) hπk (Q3TLK.fundNoncentral_model3 trivial hadm (by simp))
    ?_
  intro R R' hR hR' hne x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2
  exact absurd (OuterL4.psl4_autSq h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2) hnsq

end SL

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR
