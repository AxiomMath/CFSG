module

public import CFSG.ClassicalInvolution.Asc77.AscE189SU4
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups


theorem odd_card_galoisField_of_ne_two {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    Odd (Nat.card (GaloisField p e)) := by
  rw [GaloisField.card p e (by omega)]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem e189ModelAt_psl_four_of_odd {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    E189ModelAt p e .PSL 4 := by
  have hodd := odd_card_galoisField_of_ne_two (p := p) hp2 he
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hfund : fundamentalSubgroups .PSL (modelUniv .PSL 4 p e Fact.out).D =
      {F | ∃ g : SL(4, GaloisField p e),
        F = conjSub g (rootSL2 (GaloisField p e) two_le_four)} := by
    refine (CFSG.ClassicalInvolution.RouteD.Exotic.fundamentalSubgroups_psl_eq (p := p) (f := e)
      (m := 3) (by norm_num)).trans ?_
    ext L
    exact mem_longRootSet_iff _
  have hcl := isClassicalSL2_rootSL2 h2 two_le_four
  have key : E189AtFam SL(4, GaloisField p e)
      {F | ∃ g : SL(4, GaloisField p e),
        F = conjSub g (rootSL2 (GaloisField p e) two_le_four)} :=
    e189AtFam_of_conjClass (isUniqueInvolution_of_isClassicalSL2 hcl hodd)
      (fun c hc => conjSub_eq_of_isClassicalSL2 hcl hc)
      (fun ζ hζ hζ1 hζ2 a ha2 haz => e189SL4_std h2 hζ hζ1 hζ2 ha2 haz)
  unfold E189ModelAt modelFund ModelGrp
  rw [hfund]
  exact key

theorem e189ModelAt_psp_two_of_odd {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) : E189ModelAt p e .PSp 2 := by
  have hodd := odd_card_galoisField_of_ne_two (p := p) hp2 he
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hfund : fundamentalSubgroups .PSp (modelUniv .PSp 2 p e Fact.out).D =
      {F | ∃ g : StatedSp 2 (GaloisField p e),
        F = conjSub g (longRootSp2 (GaloisField p e) 2 0)} := by
    rw [fundamentalSubgroups_psp_eq hadm]
    ext R
    exact (exists_conj_longBlock_iff 0 R).symm
  have hcl := isClassicalSL2_longRootSp2 h2 (0 : Fin 2)
  have key : E189AtFam (StatedSp 2 (GaloisField p e))
      {F | ∃ g : StatedSp 2 (GaloisField p e),
        F = conjSub g (longRootSp2 (GaloisField p e) 2 0)} :=
    e189AtFam_of_conjClass (isUniqueInvolution_of_isClassicalSL2 hcl hodd)
      (fun c hc => conjSub_eq_of_isClassicalSL2 hcl hc)
      (fun ζ hζ hζ1 hζ2 a ha2 haz => e189Sp4_std h2 hζ hζ1 hζ2 ha2 haz)
  unfold E189ModelAt modelFund ModelGrp
  rw [hfund]
  exact key

theorem e189ModelAt_three_psl_four : E189ModelAt 3 1 .PSL 4 :=
  e189ModelAt_psl_four_of_odd (by norm_num) le_rfl

theorem e189ModelAt_three_psu_four (hadm : StatedLieAdmissible .PSU 4 3 1) :
    E189ModelAt 3 1 .PSU 4 :=
  e189ModelAt_psu_four (by norm_num) hadm

theorem e189ModelAt_three_psp_two (hadm : StatedLieAdmissible .PSp 2 3 1) :
    E189ModelAt 3 1 .PSp 2 :=
  e189ModelAt_psp_two_of_odd (by norm_num) le_rfl hadm

end CFSG.ClassicalInvolution.Q3.Q3T7E9
