module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem twinOuterAlpha_psl4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .PSL 4 p e) : TwinOuterAlpha p e .PSL 4 := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  have hπk : (proj 4 (GaloisField p e)).ker = Subgroup.center SL(4, GaloisField p e) :=
    (ker_proj (n := 4) (K := GaloisField p e)).trans (scalars_eq_center 4 (GaloisField p e))
  refine twinOuterAlphaOn_of_autVac (t := .PSL)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSL 4 p e Fact.out)
    (proj 4 (GaloisField p e)) (proj_surjective 4 (GaloisField p e)) hπk ?_
  intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4
  exact OuterL4.psl4_autVac h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4

end CFSG.ClassicalInvolution.ModelFacts.Orth15
