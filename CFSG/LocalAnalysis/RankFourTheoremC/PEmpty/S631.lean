module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.ComponentClassification Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankS smallRankR smallRankD smallRankF
  smallRankCenter KFactInnerAction Lemma628Concl Lemma629Concl Lemma630Concl Lemma631Concl
  k631_core k631_tyg_dihedral k631_le_of_sylow_centralizer sr629_F_isPGroup
  sr629_centralizer_le_normalizer_F)

private theorem s631_isKGroup_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} (hS : Situation G p P M) {a : G} (ha : a ≠ 1) :
    CFSG.IsKGroup ↥(centralizer ({a} : Set G)) := by
  have : IsSimpleGroup G := hS.simple
  refine CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
      hS.toGlobal.d1Global.kProper) _ ?_
  intro htop
  have hc : a ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact ha (by simpa [h] using hc)
  · obtain ⟨b, c, hbc⟩ := hS.nonab
    exact hbc (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) c).symm

theorem stepL631_of_kfacts (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hInn : KFactInnerAction) : StepL631 := by
  intro G _ _ p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD h29 h30
  have hp : p.Prime := hS.prime
  obtain ⟨⟨hi5, hi3, hcen⟩, -, hrank, hFe, hF4, hFinv⟩ := h29
  obtain ⟨⟨E, hEC, hEp, hEsyl, -, hEc, hE4, hEs⟩, -⟩ := h30
  obtain ⟨t, y, g, htS, hgS, hyZ, ht2, hy2, hy1, -, hgt⟩ : ∃ t y g : G,
      t ∈ smallRankS x T ∧ g ∈ smallRankS x T ∧ y ∈ smallRankCenter (smallRankS x T) ∧
      t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ t * y = y * t ∧ g * t * g⁻¹ = t * y := by
    rcases h28.1 with hp3 | hp5
    · exact absurd hp3 (by have := hS.p_ge; omega)
    · obtain ⟨n, hn⟩ := hi5 hp5
      exact k631_tyg_dihedral hn
  have hyR : y ∈ smallRankCenter (smallRankR x z T) := by
    rw [hcen]
    exact Subgroup.subset_closure ⟨hyZ, hy2⟩
  have hyF : ∀ a ∈ smallRankF p f x, y * a * y⁻¹ = a⁻¹ := hFinv y hyR hy1
  have hFp : IsPGroup f (smallRankF p f x) := sr629_F_isPGroup hfp x
  have hFE : smallRankF p f x ≤ E := k631_le_of_sylow_centralizer hfp hFp hFe.1 hEC hEp hEsyl
  have hCF := sr629_centralizer_le_normalizer_F (f := f) hp x
  have htF : t ∈ normalizer (smallRankF p f x : Set G) := hCF htS.2
  have hgF : g ∈ normalizer (smallRankF p f x : Set G) := hCF hgS.2
  have hSch' : CatalogueRelativeB.CatalogueSchreier := fun X _ _ _ hnc hcat =>
    hSch X inferInstance hnc hcat
  exact k631_core hSch' hInn hfp hf2 hS.toGlobal.d1Global.charTwo
    (fun a ha => s631_isKGroup_centralizer hS ha) hrank hEp hEs hEc hE4 hFE hFe hF4 ht2 hy1 htF
    hgF hyF hgt

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
