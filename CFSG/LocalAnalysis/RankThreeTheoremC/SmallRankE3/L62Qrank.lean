module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62NoPlane
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Catalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62QuotRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

theorem kFactThreeComponentsQRank_of_catalog (hNC : T29.NoncyclicCentreRank)
    (hQC : K3CatalogQCyc) : KFactThreeComponentsQRank := by
  intro X _ _ hcat g L hL hg3 hgL hrk
  have hH : primeComplementCore (G := Bar X) 3 = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.primeComplementCore_bar (G := X)
  have hcatH : CFSG.AGLEmbedding.CatalogSimpleSections (Bar X) :=
    hcat.quotient (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3)
  obtain ⟨L₂, L₃, hT⟩ := l62_triData hH hrk hL hg3 hgL
  have hc₂ : IsComponentOf L₂ ⊤ := hT.cyc₁ ▸ isComponentOf_map_conj hL g
  have hc₃ : IsComponentOf L₃ ⊤ := hT.cyc₂ ▸ isComponentOf_map_conj hc₂ g
  have hno : ∀ E : Subgroup ↥L, IsElemAbelian 3 E → Nat.card E = 9 → False := by
    intro E hE hE9
    refine l62_no_plane_of_triData hNC hcatH hH hrk hT hc₂ hc₃ (E := E.map L.subtype) ?_ ?_ ?_
    · rintro _ ⟨e, -, rfl⟩
      exact e.2
    · exact hE.map L.subtype
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hE9
  have hq := hL.2.2
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq
  have hcatL : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    hcatH.isCatalogGroup_center_quotient hL
  have h3 := three_dvd_card_component_quotient hH hL
  have hcyc := l62_quotient_pRank_le_one (l62_center_isPGroup hH hL) hno
  obtain ⟨q, hqp, hq5, hqd, hqM⟩ := hQC _ hsimple hnab hcatL h3 hcyc
  exact ⟨q, hqp, hq5, l62_liftQ hL hg3 hgL hrk hqp hq5 hqd hqM⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
