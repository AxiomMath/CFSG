module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverCT
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8Final
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (SLmNotOddLieInputAt CatSLmSporadicAt)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Kinds

variable {Y : Type} [Group Y]

@[expose] def NeighbourFieldKind (s : Y) (D : Subgroup Y) (m f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
      ∃ hsN : s ∈ normalizer (Kc : Set Y),
        Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
        center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f) ∧
        ∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)), IsPComponent 2 P →
          LieModel P .PSL m 2 f

@[expose] def NeighbourSwapKind (s : Y) (D : Subgroup Y) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)

theorem NeighbourOvergroupSLField.fieldKind_or_swapKind {s : Y} {D : Subgroup Y} {m f : ℕ}
    (h : NeighbourOvergroupSLField s D m f) :
    NeighbourFieldKind s D m f ∨ NeighbourSwapKind s D := by
  obtain ⟨Kc, hK, hD, hc | hc⟩ := h
  · exact .inl ⟨Kc, hK, hD, hc⟩
  · exact .inr ⟨Kc, hK, hD, hc⟩

end Kinds

section Root


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def rootTorusG (e : L ≃* adjointGroup .E6 K) : Subgroup G :=
  (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map e.symm.toMonoidHom).map
    L.subtype

@[expose] noncomputable def rootLeviG (e : L ≃* adjointGroup .E6 K) : Subgroup G :=
  ((a5Levi K).map e.symm.toMonoidHom).map L.subtype

theorem mem_centralizer_rootTorusG (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : t ∈ centralizer (L : Set G)) : t ∈ centralizer (rootTorusG e : Set G) :=
  centralizer_le (map_subtype_le _) ht

@[expose] def RootFieldKind (e : L ≃* adjointGroup .E6 K) (t : G) (f : ℕ) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    NeighbourFieldKind
      (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))))) 6 f

@[expose] def RootSwapKind (e : L ≃* adjointGroup .E6 K) (t : G) : Prop :=
  ∃ htX : t ∈ centralizer (rootTorusG e : Set G),
    NeighbourSwapKind
      (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G))) ⟨t, htX⟩)
      (((rootLeviG e).subgroupOf (centralizer (rootTorusG e : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (rootTorusG e : Set G)))))

end Root

section HR8


theorem rootFieldKind_or_rootSwapKind (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SLmNotOddLieInputAt 6) (hSpor : CatSLmSporadicAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E6 K) : RootFieldKind e t f ∨ RootSwapKind e t := by
  have htX := mem_centralizer_rootTorusG e hw.mem_centralizer
  have h := neighbour_overgroup_E6_torus_field_of_four_le_of_inputs hGLS hXodd hSpor hw.standard
    hf hw.card_eq e hw.orderOf_eq hw.inf_eq (X := rootTorusG e) (.inr rfl) htX
    (D := rootLeviG e) rfl
  rcases h.fieldKind_or_swapKind with h | h
  · exact .inl ⟨htX, h⟩
  · exact .inr ⟨htX, h⟩

end HR8

section Endgame


theorem exists_E6_fieldCoordinate (K : Type) [Field K] [Finite K] :
    ∃ χ : MulAut (adjointGroup Tag.E6 K) →* RingAut K,
      (∀ x : adjointGroup Tag.E6 K, χ (MulAut.conj x) = 1) ∧
      ∀ σ : K ≃+* K, χ (entrywiseAdjointAut Tag.E6 σ) = σ := by
  obtain ⟨Θ, -, hΘ, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  refine ⟨(MonoidHom.fst _ _).comp Θ, fun x => ?_, fun σ => ?_⟩
  · have h : Θ (MulAut.conj x) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      refine ⟨x, 1, fun h => ?_⟩
      rw [CFSG.LieType.Chevalley.rootDiagUnit_one, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_one,
        mul_one, mul_one]
    show (Θ (MulAut.conj x)).1 = 1
    rw [h]
    rfl
  · have hpos : 0 < exactE Tag.E6 := exactE_pos _
    have h := hΘ (MulAut.conj 1 * exactNormalAut Tag.E6 K 1 σ 0) 1 1 σ ⟨0, hpos⟩ fun h => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_exactNormalAut]
      simp only [mul_assoc]
    have h1 : MulAut.conj (1 : adjointGroup Tag.E6 K) * exactNormalAut Tag.E6 K 1 σ 0 =
        entrywiseAdjointAut Tag.E6 σ := by
      rw [map_one, one_mul, FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
    rw [h1] at h
    show (Θ (entrywiseAdjointAut Tag.E6 σ)).1 = σ
    rw [h]

variable {G : Type} [Group G] [Finite G] {G₀ : Subgroup G}

theorem false_of_simple_of_E6_field_quot_of_odd [IsSimpleGroup G] {f : ℕ} (hfo : Odd f)
    (K₂ : Type) [Field K₂] [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f))
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (ht : orderOf t = 2)
    (hfield : ∃ (σ : K₂ ≃+* K₂) (φ : MulAut (adjointGroup .E6 K₂)), σ ≠ 1 ∧
      φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = entrywiseAdjointAut .E6 σ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  obtain ⟨χ, hχInn, hχσ⟩ := exists_E6_fieldCoordinate K₂
  obtain ⟨hcard, hcyc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K₂ hK₂
  obtain ⟨σ, φ, hσ1, hφ⟩ := hfield
  have : Finite (RingAut K₂) :=
    Finite.of_injective (fun e : K₂ ≃+* K₂ => (e : K₂ → K₂))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  refine EPilot.false_of_simple_of_quotMulAut_hom e₀ htN ht huniq χ ?_ hχInn ?_
  · rw [hcard]
    obtain ⟨k, rfl⟩ := hfo
    omega
  · have hcomm : ∀ a b : RingAut K₂, a * b = b * a := (IsCyclic.commGroup).mul_comm
    have h1 : χ (φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹) =
        χ (normalizerQuotMulAut e₀ ⟨t, htN⟩) := by
      rw [map_mul, map_mul, map_inv, hcomm (χ φ), mul_assoc, mul_inv_cancel, mul_one]
    rw [← h1, hφ, hχσ]
    exact hσ1

end Endgame

section FieldRow


@[expose] def E6FieldCoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    RootFieldKind e t f → Nonempty (FieldNeighbourCover σ e .high)

@[expose] def E6FieldRowStep3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    RootFieldKind e t f → FieldRowCT e →
    ∀ h : G, t ∈ normalizer (CFSG.conjugate (pieceSup e) h : Set G) →
      CFSG.conjugate (pieceSup e) h ⊓ centralizer ({t} : Set G) = L →
        CFSG.conjugate (pieceSup e) h = pieceSup e

@[expose] def E6FieldEndgameEvenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (G₀ : Subgroup G) (f : ℕ), 1 ≤ f →
    Even f → ∀ (K₂ : Type) [Field K₂] [Finite K₂], Nat.card K₂ = 2 ^ (2 * f) →
    ⁅G₀, G₀⁆ = G₀ → Odd (Nat.card (center G₀)) → Odd (Nat.card (centralizer (G₀ : Set G))) →
    ∀ (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) (t : G) (htN : t ∈ normalizer (G₀ : Set G)),
    orderOf t = 2 →
    (∃ (σ : K₂ ≃+* K₂) (φ : MulAut (adjointGroup .E6 K₂)), σ ^ 2 = 1 ∧ σ ≠ 1 ∧
      φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = entrywiseAdjointAut .E6 σ) →
    (∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) → False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}

theorem false_of_fieldRow (hFC : E6FieldCoverInput) (hFam : FieldCoverFamilyInput)
    (h3 : E6FieldRowStep3Input) (hEnd : E6FieldEndgameEvenInput)
    (hq : QuadraticFrobenius K₂ σ f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E6 (fixSubfield σ))
    {t : G} (hw : F4Work L (fixSubfield σ) t f) (hk : RootFieldKind e t f) : False := by
  obtain ⟨hcov⟩ := hFC G L K₂ σ f hq hf e t hw hk
  have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hCT : FieldRowCT e := fieldRowCT_of_cover hFam hcov hq.orderOf_eq h4
  have hperf : ⁅pieceSup e, pieceSup e⁆ = pieceSup e :=
    Subgroup.isPerfect_iff.1 hCT.quasisimple.1
  have htN : t ∈ normalizer (pieceSup e : Set G) := mem_normalizer_pieceSup hw.mem_centralizer
  obtain ⟨Ψ, -⟩ := hCT.quotient
  have hK₂ : Nat.card K₂ = 2 ^ (2 * f) := hq.card_eq
  obtain ⟨⟨σ', hσ'2, hσ'1, -, φ, hφ⟩, -⟩ := inf_centralizer_eq_of_mem_normalizer_E6_cover
    hw.standard hw.card_eq e hw.orderOf_eq hw.inf_eq hperf hCT.odd_card_center hK₂ Ψ.symm htN
  have huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSup e : Set G) →
      g ∈ normalizer (pieceSup e : Set G) := by
    intro g hg
    have htM := F4Pilot.mem_normalizer_conjugate_inv hg
    have hC := inf_centralizer_conjugate_eq_E6_cover hw.standard hw.card_eq e hw.orderOf_eq
      hw.inf_eq hperf hCT.odd_card_center hK₂ Ψ.symm g⁻¹ htM
    exact F4Pilot.mem_normalizer_of_conjugate_inv_eq (h3 G L K₂ σ f hq hf e t hw hk hCT g⁻¹ htM hC)
  have := hw.standard.simple
  rcases Nat.even_or_odd f with hfe | hfo
  · have htC : t ∉ centralizer (pieceSup e : Set G) := fun htC =>
      not_inner_quot_E6 hw.standard hw.card_eq e hw.orderOf_eq hw.inf_eq hperf
        hCT.odd_card_center hK₂ Ψ.symm htN
        ⟨1, by rw [map_one, EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer Ψ.symm htN htC]⟩
    have hoddC : Odd (Nat.card (centralizer (pieceSup e : Set G))) :=
      EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hCT.le_pieceSup hw.orderOf_eq htN htC
    exact hEnd G (pieceSup e) f hw.one_le hfe K₂ hK₂ hperf hCT.odd_card_center hoddC Ψ.symm t htN
      hw.orderOf_eq ⟨σ', φ, hσ'2, hσ'1, hφ⟩ huniq
  · exact false_of_simple_of_E6_field_quot_of_odd hfo K₂ hK₂ Ψ.symm htN hw.orderOf_eq
      ⟨σ', φ, hσ'1, hφ⟩ huniq

end FieldRow

end CFSG.SeitzReduction.E6Pilot
