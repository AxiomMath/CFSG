module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


section Sp

theorem card_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem psp4_autSq3 {R R' : Subgroup (StatedSp 2 (GaloisField 3 1))}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 (GaloisField 3 1)} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)))
    (β : MulAut (StatedProj (StatedSp 2 (GaloisField 3 1))))
    (hβ : ∀ r ∈ R, β (proj 2 (GaloisField 3 1) r) = proj 2 (GaloisField 3 1) r)
    (hβ' : ∀ r ∈ R', β (proj 2 (GaloisField 3 1) r) = proj 2 (GaloisField 3 1) r) :
    β * β = 1 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  rcases Q3T8.Asc77.C25W.Sp.psp4_cent h2 card_gf3 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β
      hβ hβ' with h | h
  · rw [h, mul_one]
  · rw [h, ← map_mul, ← map_mul, hx2, map_one, map_one]

theorem twinSqAlpha3_psp (hadm : StatedLieAdmissible .PSp 2 3 1) : TwinSqAlpha 3 1 .PSp 2 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial hadm).1.1
  refine twinSqAlphaOn_of_autSq (t := .PSp) (modelUniv .PSp 2 3 1 Fact.out)
    (proj 2 (GaloisField 3 1)) proj_surjective ?_ ?_ ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · exact fund_noncentral_modelUniv trivial hadm (by simp)
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    exact psp4_autSq3
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

theorem twinOuterAlpha3_psp (hadm : StatedLieAdmissible .PSp 2 3 1) :
    TwinOuterAlpha 3 1 .PSp 2 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial hadm).1.1
  refine twinOuterAlphaOn_of_autVac (t := .PSp) (modelUniv .PSp 2 3 1 Fact.out)
    (proj 2 (GaloisField 3 1)) proj_surjective ?_ ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    left
    exact psp4_autSq3
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

end Sp

section SL

theorem twinSqAlpha3_psl (hadm : StatedLieAdmissible .PSL 4 3 1) : TwinSqAlpha 3 1 .PSL 4 :=
  twinSqAlpha_psl4_of_three (by norm_num) (by norm_num) hadm

theorem twinOuterAlpha3_psl (hadm : StatedLieAdmissible .PSL 4 3 1) :
    TwinOuterAlpha 3 1 .PSL 4 :=
  twinOuterAlpha_psl4 (by norm_num) hadm

end SL

end CFSG.ClassicalInvolution.Q3.Q3OT
