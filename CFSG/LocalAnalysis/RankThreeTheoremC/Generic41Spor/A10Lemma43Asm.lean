module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43G
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43Y
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43B
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43Case1
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDescent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_mem_normalizer_of_conj {Z : Type} [Group Z] {H : Subgroup Z} {a : Z}
    (h1 : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (h2 : ∀ h ∈ H, a⁻¹ * h * a ∈ H) :
    a ∈ Subgroup.normalizer (H : Set Z) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

theorem a10_pi_mem_normalizer {Y : Subgroup G} {g : G} (hgM : g ∈ M)
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (((Y.subgroupOf M).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) : Subgroup _) : Set _) := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := inv_mem hg
  have key : ∀ (c : G) (hcM : c ∈ M), c ∈ Subgroup.normalizer (Y : Set G) →
      ∀ w ∈ (Y.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)),
        QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨c, hcM⟩ * w *
          (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨c, hcM⟩)⁻¹ ∈
          (Y.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) := by
    intro c hcM hc w hw
    obtain ⟨z, hz, rfl⟩ := hw
    refine ⟨⟨c, hcM⟩ * z * ⟨c, hcM⟩⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.1 hc (z : G)).1 hz
  refine a10_mem_normalizer_of_conj (key g hgM hg) (fun w hw => ?_)
  have h2 := key g⁻¹ (inv_mem hgM) hginv w hw
  have e : (⟨g⁻¹, inv_mem hgM⟩ : ↥M) = (⟨g, hgM⟩ : ↥M)⁻¹ := rfl
  rw [e, map_inv, inv_inv] at h2
  exact h2

theorem a10_lemma43_asm (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI : KFactI1434) (hU : KFactU44Data) (hX : A10Facts) (hXe : A10Ext) (hL : A10L43Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (hB : A10StageB P x J ψ) {U : Subgroup G} (hUP : IIPlane 5 P x J U)
    (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore 5 M) (rankThreePrimeCore 5 M) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y hY2 hYM hUY hYB
  obtain ⟨d, hd, t₁, t₂, J₁, J₂, F, hdU, hdT, hπd, hπT, hdata⟩ :=
    a10_YData_of_G hS hD1 hU0 hX hXe hL hc ψ hψ hker hQ hB hUP hγ
  obtain ⟨hJ₁, hJ₂⟩ := a10y_components hInn hWC hSch hI hU hdata
  have hW2' : IsPGroup 2 (Y.subgroupOf M) := hY2.comap_subtype
  have hW2 : IsPGroup 2 ((Y.subgroupOf M).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5))) := hW2'.map _
  have hdn : t₁ * t₂ ∈ Subgroup.normalizer (((Y.subgroupOf M).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) : Subgroup _) : Set _) := by
    rw [← hπd]
    exact a10_pi_mem_normalizer hd (hUY hdU)
  have hB123 := a10y_B123 hJ₁ hJ₂ hdata.ne hdata.A5₁ hdata.A5₂ (Subgroup.mem_inf.1 hdata.t₁_mem).2
    (Subgroup.mem_inf.1 hdata.t₂_mem).2 hdata.t₁_ord hdata.t₂_ord hW2 hdn
  rw [← hπT] at hB123
  have hTM : u3T P x J ≤ M :=
    (inf_le_left.trans inf_le_left).trans (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hYn := a10_descent hTM hYM hB123
  exact a10_case1 hS hD1 hX hc hUP hY2 hYM hUY hYB hYn

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
