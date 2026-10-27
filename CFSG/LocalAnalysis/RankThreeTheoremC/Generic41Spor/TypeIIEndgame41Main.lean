module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41MaxPair
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eg41_false_of_plane {p : ℕ} [Fact p.Prime] (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hp : p ∈ rankThreeSigmaA G) (hp2 : p ≠ 2) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    {U : Subgroup G} (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U)
    (hF : ∀ F : Subgroup G, IsPGroup p F → U ≤ F → F ≤ M → Open.pRank p F ≤ 2 →
      IsMulCommutative F ∧ ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore p M) (rankThreePrimeCore p M) → normalizer (Y : Set G) ≤ M)
    (hL45 : ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M)
    (hL44 : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ centralizer ({x} : Set G) → X = ⊥) : False := by
  exact eg41_false_of_plane_maxpair hS hU0 hD1 hInn hWC hp hp2 hM hx1 hxp hU hUc hUP hxU
    (fun _ _ _ F hFS hUF hFM hrk => hF F hFS.isPGroup hUF hFM hrk) hC hL43 hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
