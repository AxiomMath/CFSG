module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zTYG
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yLemma628
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yLemma629
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xMain
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ComponentClassification Subgroup

variable {G : Type} [Group G] [Finite G]

theorem k631_isKGroup_centralizer (hS : Setting G) {a : G} (ha : a ≠ 1) :
    IsKGroup ↥(centralizer ({a} : Set G)) := by
  have : IsSimpleGroup G := hS.simple
  refine CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper) _ ?_
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

theorem k631_le_of_sylow_centralizer {f : ℕ} (hf : f.Prime) {F E : Subgroup G}
    (hFp : IsPGroup f F) (hFc : IsMulCommutative F) (hEC : E ≤ centralizer (F : Set G))
    (hEp : IsPGroup f E) (hEs : ¬ f ∣ (E.subgroupOf (centralizer (F : Set G))).index) :
    F ≤ E := by
  have : Fact f.Prime := ⟨hf⟩
  set K : Subgroup G := centralizer (F : Set G) with hK
  have hFK : F ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hFc.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hE'p : IsPGroup f (E.subgroupOf K) := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  have hF'p : IsPGroup f (F.subgroupOf K) := hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFK).symm
  let S : Sylow f ↥K := hE'p.toSylow hEs
  obtain ⟨S', hS'⟩ := hF'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K S S'
  intro x hx
  have hxK : x ∈ K := hFK hx
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ (F.subgroupOf K) := hx
  have h2 : (⟨x, hxK⟩ : ↥K) ∈ (S' : Subgroup ↥K) := hS' h1
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨s, hs, hsx⟩ := h2
  have hgx : g * (⟨x, hxK⟩ : ↥K) = (⟨x, hxK⟩ : ↥K) * g := by
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp g.2 x hx
    simpa using this.symm
  have hsx' : g * s * g⁻¹ = ⟨x, hxK⟩ := by simpa [MulAut.smul_def] using hsx
  have hs' : s = ⟨x, hxK⟩ := by
    have h3 : s = g⁻¹ * (⟨x, hxK⟩ : ↥K) * g := by rw [← hsx']; group
    rw [h3, mul_assoc, ← hgx]; group
  have : (⟨x, hxK⟩ : ↥K) ∈ (S : Subgroup ↥K) := hs' ▸ hs
  exact this

theorem lemma631_of_core (hS : Setting G) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hInn : KFactInnerAction) : GL83SmallRankLemma631 G := by
  intro p P M x z T hf hcov h28 f hfp hf2 hfD h29 h30
  have hp : p.Prime := hf.prime
  obtain ⟨⟨hi5, hi3, hcen⟩, -, hrank, hFe, hF4, hFinv⟩ := h29
  obtain ⟨⟨E, hEC, hEp, hEsyl, -, hEc, hE4, hEs⟩, -⟩ := h30
  obtain ⟨t, y, g, htS, hgS, hyZ, ht2, hy2, hy1, -, hgt⟩ : ∃ t y g : G,
      t ∈ smallRankS x T ∧ g ∈ smallRankS x T ∧ y ∈ smallRankCenter (smallRankS x T) ∧
      t ^ 2 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ t * y = y * t ∧ g * t * g⁻¹ = t * y := by
    rcases h28.1 with hp3 | hp5
    · obtain ⟨n, hn⟩ := hi3 hp3
      exact k631_tyg_quaternion hn
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
  exact k631_core hSch' hInn hfp hf2 hS.charTwo (fun a ha => k631_isKGroup_centralizer hS ha)
    hrank hEp hEs hEc hE4 hFE hFe hF4 ht2 hy1 htF hgF hyF hgt

theorem prop627W_of_core (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKab : KFactAbelianSylowRankThree) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hInn : KFactInnerAction) (hI : GL83SmallRankInterface G) (hK628 : KFactZAction628)
    (hK629 : KFactZAction629) (h622 : GL83SmallRankProp622 G) (h630 : GL83SmallRankLemma630 G) :
    GL83SmallRankProp627W G :=
  prop627W_of_residues hS hU0 hKab h622 (lemma628_of_interface hS hI hK628)
      (lemma629_of_interface hS hI hK629) h630 (lemma631_of_core hS hSch hInn)

end CFSG.LocalAnalysis.RankThreeTheoremC
