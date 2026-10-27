module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainOddField
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddQuot
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Span

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

omit
  [Finite G] in
theorem le_pieceSpan [Finite K] (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .F4 K) :
    L ≤ pieceSpan e := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).divisible) hct
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hle : (⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J).map φ ≤
      pieceSpan e := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    have h1 : ((CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J).map φ =
        modelToG e (rootSpan .F4 K (amalgamRoots J.1)) := by
      change (CFSG.LieType.CurtisTits.levi
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup J.1).map φ = _
      rw [levi_f4Datum_eq, modelToG, Subgroup.map_map]
    rw [h1]
    exact (modelToG_rootSpan_le_pieceCore_of_perfect e J.1
      (commutator_rootSpan_amalgamRoots_eq_of_four_le hq J.1)).trans
      (le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
        ⟨J.1, J.2⟩)
  intro l hl
  have hmem : e ⟨l, hl⟩ ∈ ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J :=
    hgen ▸ mem_top _
  have hφl : φ (e ⟨l, hl⟩) = l := by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  rw [← hφl]
  exact hle (mem_map_of_mem φ hmem)

theorem commutator_pieceSpan (e : L ≃* adjointGroup .F4 K) :
    ⁅pieceSpan e, pieceSpan e⁆ = pieceSpan e := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · refine iSup_le fun J => ?_
    have h1 : pieceCore e J.1 ≤ pieceSpan e :=
      le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1) J
    calc pieceCore e J.1 = ⁅pieceCore e J.1, pieceCore e J.1⁆ :=
          (commutator_centralizerPerfectCore _).symm
      _ ≤ ⁅pieceSpan e, pieceSpan e⁆ := commutator_mono h1 h1

theorem isPerfect_pieceSpan (e : L ≃* adjointGroup .F4 K) : Group.IsPerfect (pieceSpan e) :=
  Subgroup.isPerfect_iff.2 (commutator_pieceSpan e)

end Span

theorem odd_card_centralizer_pieceSpan {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {t : G} {f : ℕ} (hw : F4Work L K t f) (e : L ≃* adjointGroup .F4 K)
    (hLG₀ : L ≤ pieceSpan e) (htC : t ∉ centralizer (pieceSpan e : Set G)) :
    Odd (Nat.card (centralizer (pieceSpan e : Set G))) :=
  EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hLG₀ hw.orderOf_eq
    (mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1) htC

section FieldInput

@[expose] def FieldRowUniqueOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .F4 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    HR8Kind e t f .X .field → HR8Kind e t f .Y .field →
    ∀ ψ : adjointGroup .F4 K₂ →* G, Function.Injective ψ → ψ.range = pieceSpan e →
      (∀ x : adjointGroup .F4 (fixSubfield σ), ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) →
      ∀ h : G, t ∈ normalizer (conjugate (pieceSpan e) h : Set G) →
        conjugate (pieceSpan e) h ⊓ centralizer ({t} : Set G) = L →
          conjugate (pieceSpan e) h = pieceSpan e

end FieldInput

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}

theorem false_of_fieldRow_odd (hF : FieldNeighbourInput) (hU : FieldRowUniqueOddInput)
    (hq : QuadraticFrobenius K₂ σ f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    {t : G} (hw : F4Work L (fixSubfield σ) t f) (hX : HR8Kind e t f .X .field)
    (hY : HR8Kind e t f .Y .field) : False := by
  obtain ⟨hXi, hXfix⟩ := hF G L K₂ σ f hq hf e t hw .X (by decide) hX
  obtain ⟨hYi, hYfix⟩ := hF G L K₂ σ f hq hf e t hw .Y (by decide) hY
  obtain ⟨ΦX⟩ := nonempty_fieldNeighbourIso .X hXi hw.mem_centralizer hw.orderOf_eq hq.orderOf_eq
    hXfix
  obtain ⟨ΦY⟩ := nonempty_fieldNeighbourIso .Y hYi hw.mem_centralizer hw.orderOf_eq hq.orderOf_eq
    hYfix
  have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ψ, hinj, hrange, -, hfixψ⟩ := exists_injective_fieldRow ΦX ΦY h4
  have h3 := hU G L K₂ σ f hq hf e t hw hX hY ψ hinj hrange hfixψ
  let Ψ : adjointGroup .F4 K₂ ≃* pieceSpan e :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have htN : t ∈ normalizer (pieceSpan e : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1
  have htG : t ∉ pieceSpan e :=
    not_mem_F4_field hw.standard hw.card_eq e hw.mem_centralizer hw.orderOf_eq hq.card_eq Ψ.symm
  have huniq := unique_of_step3_F4_field hw.standard hw.card_eq e hw.mem_centralizer
    hw.orderOf_eq hq.card_eq Ψ.symm h3
  have : Finite (fixSubfield σ) := finite_of_natCard_eq_two_pow hw.card_eq
  have hLG₀ : L ≤ pieceSpan e := le_pieceSpan h4 e
  have htC : t ∉ centralizer (pieceSpan e : Set G) := fun htC =>
    not_exists_inner_F4_field hw.standard hw.card_eq e hw.mem_centralizer hw.orderOf_eq
      hq.card_eq Ψ.symm ⟨1, one_mem _, fun x hx => by
        rw [one_mul, inv_one, mul_one, ← mem_centralizer_iff.1 htC x hx, mul_inv_cancel_right]⟩
  have hZ := odd_card_centralizer_pieceSpan hw e hLG₀ htC
  have := hw.standard.simple
  exact false_of_simple_of_F4_field_odd hZ hq.card_eq Ψ.symm htN hw.orderOf_eq htG huniq

end FieldRow

section E6Row

@[expose] def E6RowCTQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ f ∧
      ∃ (e₆ : pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup Tag.E6 K')
        (htN : t ∈ normalizer (pieceSpan e : Set G))
        (φ : MulAut (adjointGroup Tag.E6 K')) (g : adjointGroup Tag.E6 K')
        (a : Fin Tag.E6.rank → K'ˣ) (σ' : K' ≃+* K'),
        φ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * φ⁻¹ =
          MulAut.conj g * exactNormalAut Tag.E6 K' a σ' 1

@[expose] def E6RowUniqueQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'], Nat.card K' = 2 ^ f →
      Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup Tag.E6 K') →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSpan e : Set G) →
        g ∈ normalizer (pieceSpan e : Set G)

theorem false_of_E6Row_quot (hCT : E6RowCTQuotInput) (hU : E6RowUniqueQuotInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {t : G}
    {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K)
    (hk : E6RowKinds e t f) : False := by
  obtain ⟨K', _, _, hK', e₆, htN, φ, g, a, σ', hφ⟩ := hCT G L K e t f hw hf hk
  have huniq := hU G L K e t f hw hf hk K' hK' ⟨e₆⟩
  have := hw.standard.simple
  exact EPilot.false_of_simple_of_E6_conj_graph_quot K' e₆ htN hw.orderOf_eq ⟨φ, g, a, σ', hφ⟩
    huniq

end E6Row

section TwistedE6Row

@[expose] def TwistedE6RowCTQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 ∧
      (∀ c, σ' c = c ^ (2 ^ f)) ∧
      ∃ (e₆ : pieceSpan e ⧸ center (pieceSpan e) ≃* graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom)
        (htN : t ∈ normalizer (pieceSpan e : Set G)),
        normalizerQuotMulAut e₆ ⟨t, htN⟩ ∉
          (MulAut.conj : graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom →* _).range

@[expose] def TwistedE6RowUniqueQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'] (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 →
      (∀ c, σ' c = c ^ (2 ^ f)) →
      Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃*
        graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom) →
      t ∉ pieceSpan e →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSpan e : Set G) →
        g ∈ normalizer (pieceSpan e : Set G)

theorem false_of_twistedE6Row_quot (hCT : TwistedE6RowCTQuotInput)
    (hU : TwistedE6RowUniqueQuotInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hk : TwistedE6RowKinds e t f) : False := by
  obtain ⟨K', _, _, σ', hK', hσ', e₆, htN, hout⟩ := hCT G L K e t f hw hf hk
  have htG : t ∉ pieceSpan e := EPilot.not_mem_of_normalizerQuotMulAut_not_mem_range e₆ htN hout
  have huniq := hU G L K e t f hw hf hk K' σ' hK' hσ' ⟨e₆⟩ htG
  have h4 : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC : t ∉ centralizer (pieceSpan e : Set G) := fun htC =>
    hout ⟨1, by rw [map_one, EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer e₆ htN htC]⟩
  have hZ := odd_card_centralizer_pieceSpan hw e (le_pieceSpan h4 e) htC
  have := isPerfect_pieceSpan e
  have := hw.standard.simple
  exact EPilot.false_of_simple_of_twistedE6_quot hZ hw.one_le K' hK' σ' hσ' e₆ htN
    hw.orderOf_eq hout huniq

end TwistedE6Row

section Main

theorem false_of_f4Work_of_inputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual) (hY : HR8YInput)
    (hFS : FieldSwapPieceTablesInput) (hGr : GraphPieceTablesInput) (hFN : FieldNeighbourInput)
    (hFU : FieldRowUniqueOddInput) (hSCT : SwapRowCTInput) (hSU : SwapRowUniqueInput)
    (hECT : E6RowCTQuotInput) (hEU : E6RowUniqueQuotInput) (hTCT : TwistedE6RowCTQuotInput)
    (hTU : TwistedE6RowUniqueQuotInput) (h2 : TwoRowsInput) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}
    (hq : QuadraticFrobenius K₂ σ f) (e : L ≃* adjointGroup .F4 (fixSubfield σ)) {t : G}
    (hw : F4Work L (fixSubfield σ) t f) : False := by
  have hcat : Sp6CatalogueClauses :=
    sp6CatalogueClauses_of_inputs (catSp6EvenOuter_of_exceptional_families_holds
        catSp6EvenOuterFamily_G2 catSp6EvenOuterFamily_F4 catSp6EvenOuterFamily_E6
        catSp6EvenOuterFamily_E7 catSp6EvenOuterFamily_E8 catSp6EvenOuterFamily_twistedE6
        catSp6EvenOuterFamily_trialityD4) hGLS hSp6Odd hMinn hMcomp hres
  have : CharP (fixSubfield σ) 2 := charP_two_of_natCard_eq_two_pow hw.card_eq
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by have := hw.one_le; omega
    exact false_of_two hcat h2 hw e
  · obtain ⟨κX, hκX⟩ := exists_hr8Kind_X hcat hw hf2 e
    obtain ⟨κY, hκY⟩ := exists_hr8Kind_Y hY hcat hw hf2 e
    have hcons := mem_consistentKindPairs_of_inputs hFS hGr hw hf2 e hκX hκY
    simp only [consistentKindPairs, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff,
      or_false] at hcons
    rcases hcons with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact false_of_fieldRow_odd hFN hFU hq hf2 e hw hκX hκY
    · exact false_of_swapRow hSCT hSU hw hf2 e hκX hκY
    · exact false_of_E6Row_quot hECT hEU hw hf2 e (.inl ⟨hκX, hκY⟩)
    · exact false_of_E6Row_quot hECT hEU hw hf2 e (.inr ⟨hκX, hκY⟩)
    · exact false_of_twistedE6Row_quot hTCT hTU hw hf2 e (.inl ⟨hκX, hκY⟩)
    · exact false_of_twistedE6Row_quot hTCT hTU hw hf2 e (.inr ⟨hκX, hκY⟩)

theorem seitzExclusion_highF4_of_inputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual) (hY : HR8YInput)
    (hFS : FieldSwapPieceTablesInput) (hGr : GraphPieceTablesInput) (hFN : FieldNeighbourInput)
    (hFU : FieldRowUniqueOddInput) (hSCT : SwapRowCTInput) (hSU : SwapRowUniqueInput)
    (hECT : E6RowCTQuotInput) (hEU : E6RowUniqueQuotInput) (hTCT : TwistedE6RowCTQuotInput)
    (hTU : TwistedE6RowUniqueQuotInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_forall fun _ _ _ _ _ _ _ _ _ _ hK₂ hσ hσc e _ hw =>
    false_of_f4Work_of_inputs' hGLS hSp6Odd hMinn hMcomp hres hY hFS hGr hFN hFU hSCT hSU hECT
      hEU hTCT hTU h2 ⟨hK₂, hσ, hσc⟩ e hw

end Main

end CFSG.SeitzReduction.F4Pilot
