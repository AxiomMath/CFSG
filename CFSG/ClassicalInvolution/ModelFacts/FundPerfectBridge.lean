module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem fundPerfect_modelUniv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e) :
    FundPerfect t (modelUniv t n p e Fact.out).D := by
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  exact CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund' hadm h4

theorem _root_.CFSG.ClassicalInvolution.Generic.LieSystemData.fundPerfect {p f : ℕ} [Fact p.Prime]
    {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ) (hp2 : p ≠ 2)
    (hq : 4 ≤ p ^ f) (hD4 : ∀ i, D.tag i = .trialityD4 → 4 ≤ p ^ D.exp i) (i : Fin D.card) :
    FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D := by
  refine fundPerfect_modelUniv hp2 (D.isFundTag i) (D.admissible i) ?_
  rcases D.exp_eq i with h | ⟨ht, -⟩
  · rw [h]
    exact hq
  · exact hD4 i ht

end CFSG.ClassicalInvolution.RouteD.Gaps
