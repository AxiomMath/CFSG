module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Constrained
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Shape
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Close
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Ident
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Norm
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0U3Data
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZ
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.false_of_kZeroMax_ne_of_comp (hK : KFactOneLie) (hTor : KFactOneLieTorus)
    (hSC : KFactOneLieSylowCount) (hCO : KFactOneLieCenterOver) (hPR : StmtCoprimeAutRankTwo)
    (hKU2 : KFactUnitarySylowStructure) (hKU3 : KFactUnitarySylowCenterTorus)
    (hKU4 : KFactUnitaryTorusPPD) (hKU6 : KFactUnitaryBorelMaximal)
    (hKU8 : KFactUnitarySylowNormalizerSolvable) (hKU9 : KFactUnitaryAutElemRank)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRelCyc)
    (hd : D1OneLieData p P M H R Rbar K) (hJ : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁)
    (hlt : Nat.card (nclIn H (d1LiftX p H R K)) < Nat.card (nclIn H₁ (d1LiftX p H R K)))
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
      pCoreOf 2 M ≤ H₂ →
      Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K)))
    (hcomp : ∀ (P' : Sylow p G) (S : Subgroup G), D1OneLieKZeroData p P M H R Rbar K P' H₁ S →
      ¬ HasPrimeConstraint (G := H₁) p →
      ∃ (Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
        (L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) (T₁ : Sylow p L),
        D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hne : H₁ ≠ H := by
    rintro rfl
    exact lt_irrefl _ hlt
  obtain ⟨P', S, hesc, hXS, -, -⟩ := hd.exists_sylow_of_kZero hTor hJ hH₁ hne hJH₁
  have hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S := ⟨hd, hesc, hJH₁, hXS⟩
  by_cases hcon : HasPrimeConstraint (G := H₁) p
  · exact hc.false_of_hasPrimeConstraint_of_coprimeAut hSC hPR hcon
  obtain ⟨Rb₁, L, T₁, h⟩ := hcomp P' S hc hcon
  have : L.Normal := h.normal
  obtain ⟨n, e, hTF⟩ := h.exists_torusFacts hTor
  obtain ⟨hcore₁, h3₁⟩ := h.toPhaseThree hK hTF
  have hXJ : ((d1LiftX p H R K).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_nclIn (d1LiftX_le_H p H R K)))
  have hZT := hc.centerOf_le_d1MapPCore hK h84 hD2 hY hWK h3₁ Rb₁ h.noncyclic h.borel_le
    h.not_le h.center T₁ h.sylow (h.oneLieFacts hK) hTF (hXJ.trans h.le)
  have hW := hc.d1MapPCore_le_map_liftX hK h84 hD2 hWK h3₁
  rcases h.eq_or_unitary hCO ((hZT.trans hW).trans hXJ) with hJL | ⟨hU, hcard⟩
  · obtain ⟨ψ, hψ⟩ := h.exists_mulEquiv_of_eq hJL
    exact hc.false_of_kZeroMax hK h84 hD2 hCGT hY hWK hU3 hcon h.comp h.normal hJL h.center ψ hψ
      hmax
  · obtain ⟨a, hdata⟩ := h.exists_u3Data hK hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 h84 hD2 hWK hcore₁
      h3₁ hZT hU hcard
    exact hdata.false_of h84 h85 hD2 hB3 hLB

end CFSG.AGLEmbedding
