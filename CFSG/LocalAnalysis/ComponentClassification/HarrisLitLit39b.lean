module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def IsInvolutionTwoComponent {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  ∃ a : G, orderOf a = 2 ∧ IsTwoComponentIn J (centralizer {a})

@[expose] def Harris81Lemma34Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    IsSimpleGroup ↥(Open.genFittingFStar G) → HarrisF p ↥(Open.genFittingFStar G) →
    ∀ J : Subgroup G, IsInvolutionTwoComponent J →
      (∃ p' f' : ℕ, Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f') →
        pPrimeCore 2 ↥J = ⊥

end CFSG.ComponentClassification.HarrisLit
