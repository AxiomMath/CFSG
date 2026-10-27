module

import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1PhaseThree.mem_sup_of_perfect (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hOP : KFactBlockOutPrime)
    (hSch : KFactCatalogSchreier) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hup : u ^ p = 1)
    {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVp : ⁅V, V⁆ = V)
    (hVL : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (huV : u ∈ V) :
    u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rcases blockType_ib h h85 h93 hD2 hL with htype | ⟨hcl, -, -, -⟩
  · exact hOP _ (barM M L) hL.component p h.prime hp5 htype _ hu hup
  rcases hcl with ⟨d, -, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨d, -, ⟨e⟩⟩
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL huV
  · exact hOP _ (barM M L) hL.component p h.prime hp5 (Or.inr ⟨n, Or.inr ⟨e⟩⟩) _ hu hup
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL huV

end CFSG.AGLEmbedding
