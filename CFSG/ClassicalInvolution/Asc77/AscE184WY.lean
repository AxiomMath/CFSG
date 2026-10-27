module

public import CFSG.ClassicalInvolution.Asc77.AscQuot614
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_USet_subgroupOf (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {V J Y : Subgroup G}
    (hV : V ∈ USet Ω) (hVJ : V ≤ J) (hJ : J ∈ Ω) (hJY : J ≤ Y) :
    V.subgroupOf Y ∈ USet (restrictFamily Ω Y) := by
  obtain ⟨R, -, J₁, hJ₁, hRJ₁, hVR, hcyc, hcard, h4⟩ := hΩ.exists_data_of_mem_USet hp hV
  have hJ₁J : J₁ = J :=
    hΩ.eq_of_le_of_le hJ₁ hJ (hRJ₁.2.1.to_le hVR) h4 (hVR.trans hRJ₁.1) hVJ
  subst hJ₁J
  have hVY : V ≤ Y := hVJ.trans hJY
  have hRY : R ≤ Y := hRJ₁.1.trans hJY
  have eV : V.subgroupOf Y ≃* V := Subgroup.subgroupOfEquivOfLe hVY
  have eR : R.subgroupOf Y ≃* R := Subgroup.subgroupOfEquivOfLe hRY
  refine mem_USet_of_natCard (subgroupOf_mem_restrictFamily hJ₁ hJY) (hRJ₁.subgroupOf hJY)
    (Subgroup.subgroupOf_mono Y hVR) ((MulEquiv.isCyclic eV).mpr hcyc) ?_
  rw [Nat.card_congr eR.toEquiv, Nat.card_congr eV.toEquiv]
  exact hcard

section MinCex

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.mem_eta_of_mem_USet_le (c : MinCex p f Ω K S R W H) (hM : EtaMeet Ω)
    {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) (hWη : W = ⨆ V ∈ η, V)
    (hηU : ∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) {U : Subgroup G} (hU : U ∈ USet Ω)
    (hUW : U ≤ W) : U ∈ η := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨-, hWS, -⟩ := c.stand.hW
  obtain ⟨K₀, hK₀, hUK₀⟩ := hΩ.exists_member_of_mem_USet hp hU
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
  have hUS : U ≤ (S : Subgroup G) := hUW.trans hWS
  have h2 : 2 < Nat.card ↥(K₀ ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hUK₀ hUS)
    omega
  have hmem : K₀ ⊓ (⨆ V ∈ η, V) ∈ η := hM S η hη (fun V hV => (hηU V hV).2) K₀ hK₀ h2
  rw [← hWη] at hmem
  have hV : K₀ ⊓ W ∈ USet Ω := (hηU _ hmem).1
  have hcard := hΩ.natCard_eq_of_mem_USet hp hK₀ hU hV hUK₀ inf_le_left
  have hle : U ≤ K₀ ⊓ W := le_inf hUK₀ hUW
  rw [Subgroup.eq_of_le_of_card_ge hle hcard.ge]
  exact hmem

theorem MinCex.eta_invariant (c : MinCex p f Ω K S R W H) (hM : EtaMeet Ω)
    {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) (hWη : W = ⨆ V ∈ η, V)
    (hηU : ∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) :
    ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η := by
  intro s hs U hU
  obtain ⟨-, -, hWn⟩ := c.stand.hW
  refine c.mem_eta_of_mem_USet_le hM hη hWη hηU (USet.conj c.stand.hyp.conjInvariant
    (hηU U hU).1 s) ?_
  have hUW : U ≤ W := hWη ▸ le_iSup₂_of_le U hU le_rfl
  have := conjSub_mono (n := s) hUW
  rwa [hWn s hs] at this

theorem MinCex.exists_section_W (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hS : IsSylow2In ((S : Subgroup G) ⊓ Y) Y) :
    ∃ W₁ : Subgroup ↥Y, W₁ ∈ WSet (restrictFamily Ω Y) ∧
      W₁ ≤ (AscQuot.sylowOfIsSylow2In' hS : Subgroup ↥Y) ∧
      (∀ s ∈ (AscQuot.sylowOfIsSylow2In' hS : Subgroup ↥Y), conjSub s W₁ = W₁) ∧
      W₁.map Y.subtype ≤ W := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hΩY : HypOmegaMod p f (restrictFamily Ω Y) := hΩ.restrict Y
  obtain ⟨η, hη, hWη, hηU, -, -⟩ := c.exists_eta hA
  have hinv := c.eta_invariant hM hη hWη hηU
  have hηd : InDistinctMembers Ω η := by
    obtain ⟨S₀, hS₀, -⟩ := hη
    exact hS₀.2.1
  set S₁ : Sylow 2 ↥Y := AscQuot.sylowOfIsSylow2In' hS with hS₁
  have hS₁eq : (S₁ : Subgroup ↥Y) = ((S : Subgroup G) ⊓ Y).subgroupOf Y := rfl
  have hmemS₁ : ∀ x : ↥Y, x ∈ (S₁ : Subgroup ↥Y) ↔ (x : G) ∈ (S : Subgroup G) := by
    intro x
    rw [hS₁eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  let ηY : Set (Subgroup ↥Y) :=
    {V' | V'.map Y.subtype ∈ η ∧ ∃ J ∈ Ω, J ≤ Y ∧ V'.map Y.subtype ≤ J}
  have hUS : ∀ V' ∈ ηY, V' ∈ UinS (restrictFamily Ω Y) (S₁ : Subgroup ↥Y) := by
    rintro V' ⟨hV'η, J, hJ, hJY, hVJ⟩
    refine ⟨?_, ?_⟩
    · have := mem_USet_subgroupOf hp hΩ (hηU _ hV'η).1 hVJ hJ hJY
      rwa [subgroupOf_map_subtype'] at this
    · intro x hx
      rw [hmemS₁]
      exact (hηU _ hV'η).2 ⟨x, hx, rfl⟩
  have hηYd : InDistinctMembers (restrictFamily Ω Y) ηY := by
    rintro V₁ ⟨hV₁η, -⟩ V₂ ⟨hV₂η, -⟩ hne J' hJ' ⟨h1, h2⟩
    refine hηd _ hV₁η _ hV₂η (fun h => hne (Subgroup.map_injective Y.subtype_injective h))
      (J'.map Y.subtype) (mem_restrictFamily_iff.mp hJ') ⟨Subgroup.map_mono h1,
        Subgroup.map_mono h2⟩
  have hcov : ∀ J' ∈ restrictFamily Ω Y,
      (∃ U' ∈ UinS (restrictFamily Ω Y) (S₁ : Subgroup ↥Y), U' ≤ J') → ∃ V' ∈ ηY, V' ≤ J' := by
    rintro J' hJ' ⟨U', ⟨hU'U, hU'S⟩, hU'J'⟩
    set J : Subgroup G := J'.map Y.subtype with hJdef
    have hJ : J ∈ Ω := mem_restrictFamily_iff.mp hJ'
    have hJY : J ≤ Y := Subgroup.map_subtype_le J'
    have hUU : U'.map Y.subtype ∈ USet Ω := map_mem_USet_restrict hU'U
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hUU
    have hUS' : U'.map Y.subtype ≤ (S : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hmemS₁ x).mp (hU'S hx)
    have hUJ : U'.map Y.subtype ≤ J := Subgroup.map_mono hU'J'
    have h2 : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
      have := Subgroup.card_le_of_le (le_inf hUJ hUS')
      omega
    have hmem : J ⊓ (⨆ V ∈ η, V) ∈ η := hM S η hη (fun V hV => (hηU V hV).2) J hJ h2
    rw [← hWη] at hmem
    refine ⟨(J ⊓ W).subgroupOf Y, ⟨?_, J, hJ, hJY, ?_⟩, ?_⟩
    · rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hJY)]
    · rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hJY)]
      exact inf_le_left
    · calc (J ⊓ W).subgroupOf Y ≤ J.subgroupOf Y := Subgroup.subgroupOf_mono Y inf_le_left
        _ = J' := subgroupOf_map_subtype' J'
  have hηYetaSet : ηY ∈ etaSet (restrictFamily Ω Y) (S₁ : Subgroup ↥Y) :=
    mem_etaSet_of_cover hp hΩY hUS hηYd hcov
  have hηYinv : ∀ s ∈ (S₁ : Subgroup ↥Y), ∀ V' ∈ ηY, conjSub s V' ∈ ηY := by
    rintro s hs V' ⟨hV'η, J, hJ, hJY, hVJ⟩
    have hsS : (s : G) ∈ (S : Subgroup G) := (hmemS₁ s).mp hs
    have hmap : (conjSub s V').map Y.subtype = conjSub (s : G) (V'.map Y.subtype) :=
      AscQuot.map_conjSub Y.subtype s V'
    refine ⟨?_, conjSub (s : G) J, hΩ.conjInvariant _ J hJ, ?_, ?_⟩
    · rw [hmap]
      exact hinv _ hsS _ hV'η
    · have := conjSub_mono (n := (s : G)) hJY
      rwa [conjSub_eq_self_of_mem s.2] at this
    · rw [hmap]
      exact conjSub_mono hVJ
  have hηYetaG : ηY ∈ etaG (restrictFamily Ω Y) := ⟨S₁, hηYetaSet, hηYinv⟩
  refine ⟨⨆ V' ∈ ηY, V', ⟨ηY, hηYetaG, rfl⟩, ?_, ?_, ?_⟩
  · exact iSup₂_le fun V' hV' => (hUS V' hV').2
  · intro s hs
    have hle : ∀ t ∈ (S₁ : Subgroup ↥Y), conjSub t (⨆ V' ∈ ηY, V') ≤ ⨆ V' ∈ ηY, V' := by
      intro t ht
      unfold conjSub
      rw [Subgroup.map_iSup]
      refine iSup_le fun V' => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hV' => ?_
      exact le_iSup₂_of_le _ (hηYinv t ht V' hV') le_rfl
    refine le_antisymm (hle s hs) ?_
    have := conjSub_mono (n := s) (hle s⁻¹ ((S₁ : Subgroup ↥Y).inv_mem hs))
    rwa [conjSub_conjSub_inv] at this
  · rw [Subgroup.map_iSup]
    refine iSup_le fun V' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hV' => ?_
    exact hWη ▸ le_iSup₂_of_le _ hV'.1 le_rfl

end MinCex

end CFSG.ClassicalInvolution.Asc77
