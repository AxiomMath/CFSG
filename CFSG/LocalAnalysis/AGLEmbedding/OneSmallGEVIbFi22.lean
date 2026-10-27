module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeAll
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFi22
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallGEVIbNormalAllRest3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ D1SmallOuterR p H Rbar K →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) →
    (p = 3 ∨ IsAltTwoP p K) → False

theorem d1SmallGEVIbNormalAllRest2_of_rest3 (hGst : StmtSmallGuest) (hFA : KFactFi22AltSection)
    (hK6 : KFactFi22GuestRank) (h3 : D1SmallGEVIbNormalAllRest3) :
    D1SmallGEVIbNormalAllRest2 := by
  intro G _ _ p P M H R Rbar K hd z hz hIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hcase
  rcases hcase with h | h | ⟨hp5, hFi⟩
  · exact h3 G p P M H R Rbar K hd z hz hIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
      (Or.inl h)
  · exact h3 G p P M H R Rbar K hd z hz hIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
      (Or.inr h)
  · exact hGst G p P M H R Rbar K hd (Or.inr ⟨hp5, hFi,
      mem_glbBetaFour_of_le_pRank Nat.prime_three (by norm_num) hd.cfg.ext.maxTwoLocal_H.1 le_rfl
        (four_le_pRank_of_fi22 hFA hK6 hFi)⟩)

end CFSG.AGLEmbedding
