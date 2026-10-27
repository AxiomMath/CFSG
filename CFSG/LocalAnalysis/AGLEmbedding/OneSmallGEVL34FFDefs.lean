module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def CitedFFL34BestOffender : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W), Function.Injective ρ → CFSG.IsKGroup X →
    CFSG.pCore 2 X = ⊥ → ∀ L : Subgroup X, L.Normal → ⁅L, L⁆ = L →
    IsLinThreeFour (L ⧸ primeComplementCore (G := L) 3) →
    ∀ A : Subgroup X, CFSG.IsElementaryAbelian 2 A →
      CFSG.RankThree.FFModules.IsBestOffender ρ A → A ≤ Subgroup.centralizer (L : Set X)

end CFSG.AGLEmbedding
