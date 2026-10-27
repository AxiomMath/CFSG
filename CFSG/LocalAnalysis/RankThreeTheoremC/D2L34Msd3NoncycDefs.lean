module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

@[expose] def FFGroupStep3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      ∀ L ∈ I, ∃ H₀ : Subgroup G, H₀ ≤ M ∧ L ≤ autI hU H₀ ∧
        (∀ Q : Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)),
          Q ≤ autI hU H₀ → IsPGroup 3 Q → Nat.card Q ≤ 3) ∧
        InClassG H₀ (baum T) ∧
        (IsL2OrA3Block H₀ (twoResidual H₀) →
          ∃ Y : Subgroup G, Y ≤ M ∧ IsSubnormal Y M ∧ InClassXBlock Y)

end CFSG.LocalAnalysis.RankThreeTheoremC
