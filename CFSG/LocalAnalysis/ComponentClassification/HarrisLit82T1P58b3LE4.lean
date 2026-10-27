module

public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Harris82Lemma51E4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (τ : StatedLieTag) (n p f : ℕ),
    p.Prime → p ≠ 2 → Blueprint.LieModel X τ n p f →
    ∀ z : X, orderOf z = 2 → ∀ R : Subgroup X, R ≤ centralizer {z} →
      (R.subgroupOf (centralizer {z})).IsSubnormal → z ∉ R →
      IsKleinFour (↥R ⧸ pPrimeCore 2 ↥R) →
        p ^ f = 3

end CFSG.ComponentClassification.HarrisLit.T1
