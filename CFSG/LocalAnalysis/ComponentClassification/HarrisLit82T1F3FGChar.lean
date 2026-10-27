module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGOrd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieChar

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Assembly.LowTwoRank CatLeaf CatLeafProof

section Certified


theorem false_of_lieModel_three_of_lieModel_odd {X : Type} [Group X] {τ τ' : StatedLieTag}
    {n n' f r f' : ℕ} (h3 : Blueprint.LieModel X τ n 3 f) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hXr : Blueprint.LieModel X τ' n' r f') : False := by
  have hadm3 := N36.admissible_of_lieModel' h3
  have hadmr := N36.admissible_of_lieModel' hXr
  obtain ⟨-, hord, -⟩ := lieOrderFormulasInput X τ' n' r f' hadmr hXr
  have hQ : 2 ≤ r ^ f' :=
    hadmr.1.two_le.trans (Nat.le_self_pow (by have := hadmr.2.1; omega) r)
  exact RowLie.false_of_ordProj_le (by norm_num) hadm3 h3 hord (N36.OddChar.divisor_pos hQ)
    le_rfl (divisor_mul_ordProj_three_pow_le hadmr hr2 hr3)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
