module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaAmalgam
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def D2L34AllResidue3 (P : Sylow 3 G) (M : Subgroup G) : Prop :=
  ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → D2EscapeMax 3 P M R' →
    ∃ (d' : TauCeti.ValidLieTypeIndex) (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
      D2L34BetaConf3 d' P M A' H' R' Rbar' K'

theorem D2L34AllResidue3.onlyL34At {P : Sylow 3 G} {M : Subgroup G} (h : D2L34AllResidue3 P M) :
    D2OnlyL34At P M := by
  intro A' H' R' hesc hmax Rbar' K' _ hK'
  obtain ⟨d', Rbar'', K'', hc⟩ := h A' H' R' hesc hmax
  have hKK : K' = K'' := hc.almostSimple.unique K' hK'.component
  subst hKK
  exact ⟨d', hc.l34, hc.iso⟩

@[expose] def D2L34BetaMSide3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (P : Sylow 3 G) (A H R : Subgroup G), 3 ∈ rankThreeSigmaA G →
    IsCoreMaxLocal 3 P M → ∀ (d : TauCeti.ValidLieTypeIndex)
      (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      D2L34BetaConf3 d P M A H R Rbar K → D2L34AllResidue3 P M →
      (Group.IsSolvable M → GLBStronglyEmbedded 3 M) ∧
        (GLBStronglyEmbedded 3 M → ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧
          Nat.card Q = 3 ∧ IsS3Parabolic U (U ⊔ Q) ∧
          ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H)

end CFSG.LocalAnalysis.RankThreeTheoremC
