module

public import CFSG.ClassicalInvolution.Asc77.AscT7MC
public import CFSG.ClassicalInvolution.Asc77.AscT7MA

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {e : ℕ}


theorem not_isSquare_neg_one_galoisField (hq : p ^ e % 4 = 3) (he : e ≠ 0) :
    ¬ IsSquare (-1 : GaloisField p e) := by
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  have h1 : Fintype.card (GaloisField p e) % 4 = 3 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hq
  rw [FiniteField.isSquare_neg_one_iff]
  omega

theorem isSquare_neg_one_galoisField (hq : p ^ e % 4 = 1) (he : e ≠ 0) :
    IsSquare (-1 : GaloisField p e) := by
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  have h1 : Fintype.card (GaloisField p e) % 4 = 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hq
  rw [FiniteField.isSquare_neg_one_iff]
  omega

theorem twinSqAlpha_psl4_of_three (hp2 : p ≠ 2) (hq : p ^ e % 4 = 3)
    (hadm : StatedLieAdmissible .PSL 4 p e) : TwinSqAlpha p e .PSL 4 := by
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hnsq := not_isSquare_neg_one_galoisField (p := p) hq (by have := hadm.2.1; omega)
  have : Group.IsPerfect (modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  have hπk : (proj 4 (GaloisField p e)).ker = Subgroup.center SL(4, GaloisField p e) :=
    (ker_proj (n := 4) (K := GaloisField p e)).trans (scalars_eq_center 4 (GaloisField p e))
  refine twinSqAlphaOn_of_autSq (t := .PSL) (modelUniv .PSL 4 p e Fact.out)
    (proj 4 (GaloisField p e)) (proj_surjective 4 (GaloisField p e)) hπk
    (fund_noncentral_modelUniv trivial hadm (by simp)) ?_
  intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2
  exact absurd (OuterL4.psl4_autSq h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2) hnsq

end CFSG.ClassicalInvolution.Asc77
