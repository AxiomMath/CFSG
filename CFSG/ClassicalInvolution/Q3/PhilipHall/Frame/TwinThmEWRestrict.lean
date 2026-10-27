module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Restrict



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem inDistinct_canonical (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    InDistinctMembers Ω {U | U ∈ USet Ω ∧ U ≤ W} := by
  obtain ⟨η, ⟨S₁, hS₁, hinv⟩, hWη⟩ := hW
  have := (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hS₁ hinv).2
  rw [hWη, this]
  exact hS₁.2.1

theorem mem_USet_restrict_of_le (hΩ : HypOmegaGen Ω) {Y L U : Subgroup G} (hU : U ∈ USet Ω)
    (hL : L ∈ Ω) (hLY : L ≤ Y) (hUL : U ≤ L) : U.subgroupOf Y ∈ USet (restrictFamily Ω Y) := by
  have hdat := hΩ.exists_data_of_mem_USet hU
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hdat
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJL : L = J := hΩ.eq_of_le_of_le hL hJ (hRJ.2.1.to_le hUR) h4 hUL (hUR.trans hRJ.1)
  subst hJL
  exact CFSG.ClassicalInvolution.Asc77.AscAET.mem_USet_restrict_of_sylow hL hLY hRJ hUR hcyc hidx

theorem mem_sylow_of_mem {Y : Subgroup G} {S' : Sylow 2 G} {S₁ : Sylow 2 ↥Y}
    (hS₁ : (S₁ : Subgroup ↥Y).map Y.subtype ≤ (S' : Subgroup G)) {x : ↥Y}
    (hx : (x : G) ∈ (S' : Subgroup G)) : x ∈ (S₁ : Subgroup ↥Y) := by
  have h2 : IsPGroup 2 ↥((S' : Subgroup G).subgroupOf Y) := S'.isPGroup'.comap_subtype
  have hle : (S₁ : Subgroup ↥Y) ≤ (S' : Subgroup G).subgroupOf Y := fun y hy =>
    hS₁ ⟨y, hy, rfl⟩
  have heq := S₁.is_maximal' h2 hle
  have hx' : x ∈ (S' : Subgroup G).subgroupOf Y := hx
  rw [heq] at hx'
  exact hx'

theorem commutes_or_eq_map_subtype {Y : Subgroup G} {R₁ R₂ : Subgroup ↥Y}
    (h : Commutes R₁ R₂ ∨ R₂ = R₁) :
    Commutes (R₁.map Y.subtype) (R₂.map Y.subtype) ∨ R₂.map Y.subtype = R₁.map Y.subtype := by
  rcases h with h | h
  · refine Or.inl ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (h x hx y hy)
  · exact Or.inr (by rw [h])

theorem exists_W_restrict (hΩ : HypOmegaGen Ω) {Y : Subgroup G} {S' : Sylow 2 G}
    {W' H : Subgroup G} (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') (hCW : CentPairs Ω (S' : Subgroup G) W' H)
    {S₁ : Sylow 2 ↥Y} (hS₁ : (S₁ : Subgroup ↥Y).map Y.subtype ≤ (S' : Subgroup G)) :
    ∃ W₁ ∈ WSet (restrictFamily Ω Y), W₁ ≤ (S₁ : Subgroup ↥Y) ∧
      (∀ s ∈ (S₁ : Subgroup ↥Y), conjSub s W₁ = W₁) ∧
      CentPairs (restrictFamily Ω Y) (S₁ : Subgroup ↥Y) W₁ (H.subgroupOf Y) := by
  classical
  have hΛ : HypOmegaGen (restrictFamily Ω Y) := hypOmegaGen_restrict hΩ Y
  have hdist := inDistinct_canonical hΩ hW'
  set η₁ : Set (Subgroup ↥Y) := {V | V ∈ USet (restrictFamily Ω Y) ∧ V ≤ (S₁ : Subgroup ↥Y) ∧
    V.map Y.subtype ≤ W'} with hη₁def
  have hmemS : ∀ x : ↥Y, (x : G) ∈ (S' : Subgroup G) → x ∈ (S₁ : Subgroup ↥Y) :=
    fun x hx => mem_sylow_of_mem hS₁ hx
  have hS₁S' : ∀ x ∈ (S₁ : Subgroup ↥Y), (x : G) ∈ (S' : Subgroup G) := fun x hx =>
    hS₁ ⟨x, hx, rfl⟩
  have h4 : ∀ V ∈ USet (restrictFamily Ω Y), 4 ≤ Nat.card V := fun V hV => by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hΛ.exists_data_of_mem_USet hV
    exact h
  have hcardmap : ∀ V : Subgroup ↥Y, Nat.card ↥(V.map Y.subtype) = Nat.card V := fun V =>
    (Nat.card_congr (Subgroup.equivMapOfInjective V Y.subtype Y.subtype_injective).toEquiv).symm
  have hη₁dist : InDistinctMembers (restrictFamily Ω Y) η₁ := by
    intro V hV V' hV' hne L hL hVV'
    have hLΩ : L.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hL
    exact hdist (V.map Y.subtype) ⟨map_mem_USet_restrict hV.1, hV.2.2⟩ (V'.map Y.subtype)
      ⟨map_mem_USet_restrict hV'.1, hV'.2.2⟩
      (fun h => hne (Subgroup.map_injective Y.subtype_injective h)) (L.map Y.subtype) hLΩ
      ⟨Subgroup.map_mono hVV'.1, Subgroup.map_mono hVV'.2⟩
  have hmax : ∀ η₂ : Set (Subgroup ↥Y),
      η₂ ⊆ {V | V ∈ USet (restrictFamily Ω Y) ∧ V ≤ (S₁ : Subgroup ↥Y)} →
      InDistinctMembers (restrictFamily Ω Y) η₂ → η₂.ncard ≤ η₁.ncard := by
    intro η₂ hsub hd2
    have hmem : ∀ V ∈ η₂, ∃ L₀ : Subgroup G, L₀ ∈ Ω ∧ L₀ ≤ Y ∧ V ≤ L₀.subgroupOf Y := by
      intro V hV
      obtain ⟨J, hJ, hVJ⟩ := Sec6Gen.exists_member_of_mem_USet hΛ (hsub hV).1
      exact ⟨J.map Y.subtype, mem_restrictFamily_iff.mp hJ, Subgroup.map_subtype_le J,
        by rwa [subgroupOf_map_subtype']⟩
    choose! L₀ hL₀Ω hL₀Y hVL₀ using hmem
    have hkey : ∀ V ∈ η₂, (L₀ V ⊓ W') ∈ USet Ω := by
      intro V hV
      have hVM : V.map Y.subtype ≤ L₀ V := by
        have := Subgroup.map_mono (f := Y.subtype) (hVL₀ V hV)
        rwa [Subgroup.map_subgroupOf_eq_of_le (hL₀Y V hV)] at this
      have hVS : V.map Y.subtype ≤ (S' : Subgroup G) :=
        (Subgroup.map_mono (hsub hV).2).trans hS₁
      have hc := Subgroup.card_le_of_le (le_inf hVM hVS)
      have h4V := h4 V (hsub hV).1
      rw [hcardmap V] at hc
      exact inf_W_mem_USet_of_card hΩ hW' hW'S (hL₀Ω V hV) (by omega)
    have hmaps : Set.MapsTo (fun V => (L₀ V ⊓ W').subgroupOf Y) η₂ η₁ := by
      intro V hV
      have hUinf := hkey V hV
      have hM := hL₀Ω V hV
      have hMY := hL₀Y V hV
      refine ⟨mem_USet_restrict_of_le hΩ hUinf hM hMY inf_le_left, ?_, ?_⟩
      · intro x hx
        exact hmemS x (hW'S (Subgroup.mem_subgroupOf.mp hx).2)
      · rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hMY)]
        exact inf_le_right
    have hinj : Set.InjOn (fun V => (L₀ V ⊓ W').subgroupOf Y) η₂ := by
      intro V₁ hV₁ V₂ hV₂ h
      by_contra hne
      have h' : L₀ V₁ ⊓ W' = L₀ V₂ ⊓ W' := by
        have := congrArg (Subgroup.map Y.subtype) h
        rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans (hL₀Y V₁ hV₁)),
          Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans (hL₀Y V₂ hV₂))] at this
      have hU := hkey V₁ hV₁
      obtain ⟨-, -, -, -, -, -, -, -, h4U⟩ := hΩ.exists_data_of_mem_USet hU
      have hM : L₀ V₁ = L₀ V₂ := hΩ.eq_of_le_of_le (hL₀Ω V₁ hV₁) (hL₀Ω V₂ hV₂)
        (hΩ.isPGroup_of_mem_USet hU) h4U inf_le_left (h' ▸ inf_le_left)
      have hVV₂ : V₂ ≤ (L₀ V₁).subgroupOf Y := hM ▸ hVL₀ V₂ hV₂
      exact hd2 V₁ hV₁ V₂ hV₂ hne ((L₀ V₁).subgroupOf Y)
        (subgroupOf_mem_restrictFamily (hL₀Ω V₁ hV₁) (hL₀Y V₁ hV₁)) ⟨hVL₀ V₁ hV₁, hVV₂⟩
    exact Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  have hη₁S : η₁ ∈ etaSet (restrictFamily Ω Y) (S₁ : Subgroup ↥Y) :=
    ⟨fun V hV => ⟨hV.1, hV.2.1⟩, hη₁dist, hmax⟩
  have hinv : ∀ s ∈ (S₁ : Subgroup ↥Y), ∀ V ∈ η₁, conjSub s V ∈ η₁ := by
    intro s hs V hV
    refine ⟨USet.conj hΛ.conjInvariant hV.1 s, ?_, ?_⟩
    · have := conjSub_mono (n := s) hV.2.1
      rwa [conjSub_eq_self_of_mem hs] at this
    · have e := conjSub_map Y.subtype s V
      rw [← e]
      have := conjSub_mono (n := (s : G)) hV.2.2
      rwa [hW'n (s : G) (hS₁S' s hs)] at this
  have hW₁mem : (⨆ V ∈ η₁, V) ∈ WSet (restrictFamily Ω Y) := ⟨η₁, ⟨S₁, hη₁S, hinv⟩, rfl⟩
  have hW₁S : (⨆ V ∈ η₁, V) ≤ (S₁ : Subgroup ↥Y) := iSup₂_le fun V hV => hV.2.1
  have hW₁le : (⨆ V ∈ η₁, V) ≤ W'.comap Y.subtype := iSup₂_le fun V hV =>
    (Subgroup.map_le_iff_le_comap).mp hV.2.2
  refine ⟨_, hW₁mem, hW₁S, ?_, ?_⟩
  · intro s hs
    rw [conjSub_iSup₂]
    apply le_antisymm
    · exact iSup₂_le fun U hU => le_iSup₂_of_le _ (hinv s hs U hU) le_rfl
    · refine iSup₂_le fun U hU => ?_
      have hU' : conjSub s⁻¹ U ∈ η₁ := hinv s⁻¹ ((S₁ : Subgroup ↥Y).inv_mem hs) U hU
      have : U = conjSub s (conjSub s⁻¹ U) := (conjSub_conjSub_inv s U).symm
      rw [this]
      exact le_iSup₂_of_le (conjSub s⁻¹ U) hU' le_rfl
  · intro M₁ hM₁ hMW
    have hM₀ : M₁.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hM₁
    have hVS : M₁ ⊓ (⨆ V ∈ η₁, V) ≤ (S₁ : Subgroup ↥Y) := inf_le_right.trans hW₁S
    have hc := Subgroup.card_le_of_le
      (le_inf ((Subgroup.map_mono (inf_le_left : M₁ ⊓ (⨆ V ∈ η₁, V) ≤ M₁)))
        ((Subgroup.map_mono hVS).trans hS₁))
    rw [hcardmap] at hc
    have h4V := h4 _ hMW
    have hMW' : M₁.map Y.subtype ⊓ W' ∈ USet Ω :=
      inf_W_mem_USet_of_card hΩ hW' hW'S hM₀ (by omega)
    have hC := hCW _ hM₀ hMW'
    intro J₁ hJ₁ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm a haR haW ha1 ha2
    have hkp := kPerp_map hJ₁
    have haG : (a : G) ∈ R₁.map Y.subtype ⊔ R₂.map Y.subtype := by
      have : (a : G) ∈ (R₁ ⊔ R₂).map Y.subtype := ⟨a, haR, rfl⟩
      rwa [Subgroup.map_sup] at this
    have hC' := hC _ hkp _ _ (map_mem_RSet_restrict hR₁) (Subgroup.map_mono hR₁M)
      ((Subgroup.map_mono hR₁S).trans hS₁) (map_mem_RSet_restrict hR₂) (Subgroup.map_mono hR₂J)
      ((Subgroup.map_mono hR₂S).trans hS₁) (commutes_or_eq_map_subtype hcomm) (a : G) haG
      (hW₁le haW) (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have : (y : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hy
    exact Subgroup.mem_subgroupOf.mpr (hC' this)

end Restrict


end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
