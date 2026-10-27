module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Facts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup


@[expose] def KD291a3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (P : Sylow p X) (x z : X), Plane63 p X P x z →
    ∀ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ →
      (∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
      CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set X))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
