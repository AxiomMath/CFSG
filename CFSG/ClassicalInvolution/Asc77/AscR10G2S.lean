module

public import CFSG.ClassicalInvolution.Asc77.AscR10Q9Main
public import CFSG.ClassicalInvolution.Uniform.ULieSystemIff

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911



section Layer

variable {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}

theorem omegaGen_restrictFamily_self : omegaGen (restrictFamily Λ (omegaGen Λ)) = ⊤ := by
  set H := omegaGen Λ with hH
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  apply le_antisymm
  · exact Subgroup.map_le_range _ _ |>.trans (by rw [Subgroup.range_subtype])
  · refine iSup₂_le fun L hL => ?_
    have hLH : L ≤ H := le_omegaGen hL
    calc L = (L.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hLH).symm
      _ ≤ (omegaGen (restrictFamily Λ H)).map H.subtype :=
        Subgroup.map_mono (le_omegaGen ⟨L, hL, hLH, rfl⟩)

theorem inClass3_layer (hΩ : HypOmegaModU (.sl2 3 1) Λ) (hne : Λ.Nonempty) :
    Q3.InClass3 (restrictFamily Λ (omegaGen Λ)) where
  nonempty := by
    obtain ⟨K, hK⟩ := hne
    exact ⟨K.subgroupOf (omegaGen Λ), K, hK, le_omegaGen hK, rfl⟩
  conjInvariant := by
    intro n K' hK'
    rw [mem_restrictFamily_iff] at hK' ⊢
    have h1 : (conjSub n K').map (omegaGen Λ).subtype =
        conjSub (n : Y) (K'.map (omegaGen Λ).subtype) := by
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1]
    exact hΩ.conjInvariant _ _ hK'
  generated := by
    have := omegaGen_restrictFamily_self (Λ := Λ)
    unfold omegaGen at this
    exact this
  classical := by
    intro K' hK'
    rw [mem_restrictFamily_iff] at hK'
    obtain ⟨z, hz⟩ := hΩ.classical _ hK'
    have hle : K'.map (omegaGen Λ).subtype ≤ omegaGen Λ := Subgroup.map_subtype_le K'
    have h1 := hz.subgroupOf hle
    have h2 : (K'.map (omegaGen Λ).subtype).subgroupOf (omegaGen Λ) = K' :=
      Subgroup.comap_map_eq_self_of_injective (omegaGen Λ).subtype_injective K'
    rw [h2] at h1
    exact ⟨_, h1.toQ3 (by norm_num)⟩

end Layer

section Comp

theorem ih8Model_of_comp_g2 {E : Type} [Group E] {Ω : Set (Subgroup E)}
    (hconj : ConjInvariant Ω) {c : Q3.CompData} (hc : c = compModel 3 1 .G2 0) (φ : c.G →* E)
    (hker : φ.ker ≤ Subgroup.center c.G) (hsurj : Function.Surjective φ)
    (hfund : ∀ L ∈ Ω, ∃ R ∈ c.fund, L = R.map φ) : Nonempty (Ih8Model 3 1 Ω .G2 0 1) :=
  ⟨{ isFundTag := trivial
     admissible := ⟨Nat.prime_three, le_refl 1, rfl, by norm_num⟩
     exp_eq := Or.inl rfl
     ψ := castHom hc φ
     ker_le_center := castHom_ker_le_center hc φ hker
     surj := by
       rw [← MonoidHom.range_eq_top] at hsurj ⊢
       rw [range_castHom]
       exact hsurj
     cls := {R | R ∈ fundamentalSubgroups .G2 (modelUniv .G2 0 3 1 Fact.out).D ∧
       R.map (castHom hc φ) ∈ Ω}
     cls_sub := fun _ hR => hR.1
     mem_iff := by
       intro L
       constructor
       · intro hL
         obtain ⟨R, hR, rfl⟩ := hfund L hL
         obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc φ hR
         exact ⟨R', ⟨hR', by rw [hRR]; exact hL⟩, hRR.symm⟩
       · rintro ⟨R, hR, rfl⟩
         exact hR.2
     cls_conj := by
       intro R hR g
       refine ⟨Asc77.OmegaLie.fund_conj hR.1 g, ?_⟩
       have := map_conj_eq_conjSub_map (castHom hc φ) g R
       change Subgroup.map (castHom hc φ) (conjSub g R) ∈ Ω
       rw [show Subgroup.map (castHom hc φ) (conjSub g R) =
         conjSub (castHom hc φ g) (R.map (castHom hc φ)) from this]
       exact hconj _ _ hR.2 }⟩

theorem comp_g2_facts {c : Q3.CompData} (hc : c = compModel 3 1 .G2 0) :
    IsSimpleGroup c.G ∧ Subgroup.center c.G = ⊥ ∧
      ∀ {X : Type} [Group X] (φ : c.G →* X), φ.ker ≤ Subgroup.center c.G →
        Function.Injective φ := by
  subst hc
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 :=
    ⟨Nat.prime_three, le_refl 1, rfl, by norm_num⟩
  have hi : ((CFSG.Assembly.LowTwoRank.StatedLieTag.G2 : CFSG.Assembly.LowTwoRank.StatedLieTag) =
      .G2 ∨ (CFSG.Assembly.LowTwoRank.StatedLieTag.G2 : CFSG.Assembly.LowTwoRank.StatedLieTag) =
      .trialityD4) := Or.inl rfl
  exact ⟨T3Typed.isSimpleGroup_model_of_g2d4 hp2 hadm hi,
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 hi 0 le_rfl,
    fun φ hφ => RouteD.G2D4.injective_of_ker_le_center hp2 hi 0 le_rfl φ hφ⟩

end Comp


section Main

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem mem_oddCore_layer_iff {L : Subgroup Y} [L.Normal] (x : ↥L) :
    x ∈ classicalInvolutionOddCore ↥L ↔ (x : Y) ∈ classicalInvolutionOddCore Y := by
  have h := CFSG.ComponentClassification.OddCore.normal_intersection Y L
  constructor
  · intro hx
    have hx' : (x : Y) ∈ (classicalInvolutionOddCore ↥L).map L.subtype := ⟨x, hx, rfl⟩
    have h1 : (classicalInvolutionOddCore ↥L).map L.subtype = L ⊓ classicalInvolutionOddCore Y := h
    rw [h1] at hx'
    exact hx'.2
  · intro hx
    have h1 : (classicalInvolutionOddCore ↥L).map L.subtype = L ⊓ classicalInvolutionOddCore Y := h
    have hmem : (x : Y) ∈ (classicalInvolutionOddCore ↥L).map L.subtype := by
      rw [h1]
      exact ⟨x.2, hx⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

@[expose] noncomputable def layerHom (L : Subgroup Y) [L.Normal] :
    (↥L ⧸ classicalInvolutionOddCore ↥L) →* (Y ⧸ classicalInvolutionOddCore Y) :=
  QuotientGroup.lift (classicalInvolutionOddCore ↥L) ((oddQuot Y).comp L.subtype)
    (fun x hx => (QuotientGroup.eq_one_iff _).mpr ((mem_oddCore_layer_iff x).mp hx))

theorem layerHom_mk (L : Subgroup Y) [L.Normal] (x : ↥L) :
    layerHom L (QuotientGroup.mk x) = oddQuot Y (x : Y) := rfl

theorem layerHom_injective (L : Subgroup Y) [L.Normal] : Function.Injective (layerHom L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : oddQuot Y (x : Y) = 1 := hq
  exact (QuotientGroup.eq_one_iff x).mpr ((mem_oddCore_layer_iff x).mpr
    ((QuotientGroup.eq_one_iff _).mp h1))

theorem sectionG2_of_single (hΩ : HypOmegaModU (.sl2 3 1) Λ) {K : Subgroup Y} (hK : K ∈ Λ)
    {L : Subgroup Y} [hLn : L.Normal] (hΛL : ∀ M ∈ Λ, M ≤ L) {ι : Type}
    (D : Q3.LieSystemData3 ι (↥L ⧸ classicalInvolutionOddCore ↥L)
      (oddQuotientFamily (restrictFamily Λ L)))
    {i : ι} (hi : ∀ j : ι, j = i) (hk : D.kind i = Q3.CompData.model .G2 0) :
    SectionG2 Λ K := by
  classical
  have hc : D.kind i = compModel 3 1 .G2 0 := hk
  let θ := layerHom L
  have hθinj : Function.Injective θ := layerHom_injective L
  let E : Subgroup (Y ⧸ classicalInvolutionOddCore Y) := L.map (oddQuot Y)
  have hEn : E.Normal := Subgroup.Normal.map hLn (oddQuot Y) (QuotientGroup.mk'_surjective _)
  have hθE : ∀ q, θ q ∈ E := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, x.2, rfl⟩
  have hθEsurj : ∀ e : ↥E, ∃ q, θ q = e := by
    rintro ⟨e, y, hy, rfl⟩
    exact ⟨QuotientGroup.mk ⟨y, hy⟩, rfl⟩
  let θE : (↥L ⧸ classicalInvolutionOddCore ↥L) →* ↥E := θ.codRestrict E hθE
  have hθEinj : Function.Injective θE := fun a b h => hθinj (congrArg Subtype.val h)
  have hθEsurj' : Function.Surjective θE := fun e => by
    obtain ⟨q, hq⟩ := hθEsurj e
    exact ⟨q, Subtype.ext hq⟩
  have hrange' : (⨆ j, (D.hom j).range) = (D.hom i).range :=
    le_antisymm (iSup_le fun j => by rw [hi j]) (le_iSup (fun j => (D.hom j).range) i)
  have hsurj : Function.Surjective (D.hom i) := by
    apply MonoidHom.range_eq_top.mp
    rw [← hrange', D.generate]
  obtain ⟨hsimple, -, hinj⟩ := comp_g2_facts hc
  let φ : (D.kind i).G →* ↥E := θE.comp (D.hom i)
  have hφinj : Function.Injective φ := hθEinj.comp (hinj (D.hom i) (D.ker_le_center i))
  have hφsurj : Function.Surjective φ := hθEsurj'.comp hsurj
  have hS : IsSimpleGroup ↥E := by
    have := hsimple
    exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ :
      (D.kind i).G ≃* ↥E).symm
  have hKE : K.map (oddQuot Y) ≤ E := Subgroup.map_mono (hΛL K hK)
  have hconj : ConjInvariant (restrictFamily (oddQuotientFamily Λ) E) := by
    intro n M' hM'
    rw [mem_restrictFamily_iff] at hM' ⊢
    obtain ⟨M₀, hM₀, hM₀e⟩ := hM'
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (n : Y ⧸ classicalInvolutionOddCore Y)
    have h1 : (conjSub n M').map E.subtype = conjSub (n : Y ⧸ classicalInvolutionOddCore Y)
        (M'.map E.subtype) := by
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, ← hM₀e, ← hy]
    refine ⟨conjSub y M₀, hΩ.conjInvariant y M₀ hM₀, ?_⟩
    exact AscQuot.map_conjSub (oddQuot Y) y M₀
  have hfund : ∀ M' ∈ restrictFamily (oddQuotientFamily Λ) E,
      ∃ R ∈ (D.kind i).fund, M' = R.map φ := by
    intro M' hM'
    rw [mem_restrictFamily_iff] at hM'
    obtain ⟨M₀, hM₀, hM₀e⟩ := hM'
    have hle : M₀ ≤ L := hΛL M₀ hM₀
    have hM₁mem : M₀.subgroupOf L ∈ restrictFamily Λ L := ⟨M₀, hM₀, hle, rfl⟩
    have hMt : (M₀.subgroupOf L).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) ∈
        oddQuotientFamily (restrictFamily Λ L) := ⟨_, hM₁mem, rfl⟩
    obtain ⟨j, R, hR, hMR⟩ := D.fundamental _ hMt
    obtain rfl := hi j
    refine ⟨R, hR, ?_⟩
    apply Subgroup.map_injective E.subtype_injective
    have h1 : (R.map φ).map E.subtype = (R.map (D.hom j)).map θ := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, ← hMR, Subgroup.map_map, ← hM₀e]
    have h2 : θ.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) =
        (oddQuot Y).comp L.subtype := rfl
    rw [h2, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle]
  obtain ⟨M⟩ := ih8Model_of_comp_g2 hconj hc φ (by
    intro x hx
    have := hφinj (by rw [MonoidHom.mem_ker.mp hx, map_one] : φ x = φ 1)
    rw [this]; exact Subgroup.one_mem _) hφsurj hfund
  exact ⟨E, hEn, hS, hKE, ⟨M⟩⟩

@[expose] def G2Sec3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), HypOmegaModU (.sl2 3 1) Λ →
    (∀ M₁ ∈ Λ, ∀ M₂ ∈ omegaNbr Λ M₁, M₂ ∈ twinSet Λ M₁) →
    ∀ (K J : Subgroup Y) (zK zJ : Y), K ∈ Λ → AViol Λ K J zK zJ →
      ∀ {ι : Type} (D : Q3.LieSystemData3 ι
        (↥(omegaGen Λ) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ))
        (oddQuotientFamily (restrictFamily Λ (omegaGen Λ)))),
        ∃ i : ι, (∀ j : ι, j = i) ∧ D.kind i = Q3.CompData.model .G2 0

theorem sec3Typing_of_g2Sec3 (h3 : Q3.CIT3Inductive) (hG : G2Sec3) : Sec3Typing := by
  intro Y _ _ Λ hΩ htw K J zK zJ hK hv
  have hLn : (omegaGen Λ).Normal := omegaGen_normal hΩ.conjInvariant
  have hIn := inClass3_layer hΩ ⟨K, hK⟩
  obtain ⟨ι, -, ⟨D⟩⟩ := h3 ↥(omegaGen Λ) (restrictFamily Λ (omegaGen Λ)) hIn
  obtain ⟨i, hi, hk⟩ := hG Y Λ hΩ htw K J zK zJ hK hv D
  exact sectionG2_of_single hΩ hK (fun M hM => le_omegaGen hM) D hi hk

theorem res10aNoConj_nine_of_g2Sec3 (p f : ℕ) [Fact p.Prime] (h3 : Q3.CIT3Inductive)
    (hG : G2Sec3) (h9 : p ^ f = 9) : Res10aNoConj p f :=
  res10aNoConj_nine_of_typing p f (sec3Typing_of_g2Sec3 h3 hG) h9

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII
