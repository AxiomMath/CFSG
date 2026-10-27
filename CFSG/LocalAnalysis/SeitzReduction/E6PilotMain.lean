module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (SLmNotOddLieInputAt CatSLmSporadicAt slmCatalogueClausesAt_six)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius)

section SwapRow

@[expose] def E6SwapRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    RootSwapKind e t →
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      Nonempty (G₁ ⧸ center G₁ ≃* adjointGroup .E6 (fixSubfield σ)) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e

@[expose] def E6SwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    RootSwapKind e t →
    ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      Nonempty (G₁ ⧸ center G₁ ≃* adjointGroup .E6 (fixSubfield σ)) →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSup e : Set G) →
        g ∈ normalizer (pieceSup e : Set G)

theorem false_of_swapRow (hCT : E6SwapRowCTInput) (hU : E6SwapRowUniqueInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    {σ : K₂ ≃+* K₂} {f : ℕ} (hq : QuadraticFrobenius K₂ σ f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {t : G} (hw : F4Work L (fixSubfield σ) t f)
    (hk : RootSwapKind e t) : False := by
  obtain ⟨G₁, hqs, hiso, h₁₂, hsup⟩ := hCT G L K₂ σ f hq hf e t hw hk
  have huniq := hU G L K₂ σ f hq hf e t hw hk G₁ hqs hiso h₁₂ hsup
  have := hw.standard.simple
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple hw.orderOf_eq hqs h₁₂ rfl
    (by rw [hsup]; exact huniq)

end SwapRow

section Two

@[expose] def E6TwoPositionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E6 K) (t : G), F4Work L K t 1 →
    ∀ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K → IsCyclic A → Nat.card A = 3 →
      ¬ (((rootLeviG e).subgroupOf
          (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))).map
        (QuotientGroup.mk' (oddCore
          (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))))).Normal

@[expose] def E6TwoRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E6 K) (t : G), F4Work L K t 1 →
    ∀ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K → IsCyclic A → Nat.card A = 3 →
    ∀ htX : t ∈ centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G),
      NeighbourOvergroupSLField
        (QuotientGroup.mk' (oddCore
          (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))) ⟨t, htX⟩)
        (((rootLeviG e).subgroupOf
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))).map
          (QuotientGroup.mk' (oddCore
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))))) 6 1 → False

theorem false_of_two (hGLS : GLS3OddLieAutComponentsInput) (hXodd : SLmNotOddLieInputAt 6)
    (hSpor : CatSLmSporadicAt 6) (hpos : E6TwoPositionInput) (hrows : E6TwoRowsInput)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .E6 K) : False := by
  obtain ⟨A, hAJ, hcyc, hA⟩ := exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E6) (K := K)
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hA3 : Nat.card A = 3 := by rw [hA, hK2]
  have htX : t ∈ centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G) :=
    centralizer_le (map_subtype_le _) hw.mem_centralizer
  have hnn := hpos G L K e t hw A hAJ hcyc hA3
  have hNO := neighbour_overgroup_E6_nonsplit_field_of_not_normal
    (slmCatalogueClausesAt_six hGLS hXodd hSpor) hw.standard hw.card_eq e hw.orderOf_eq hw.inf_eq
    hAJ hA hcyc rfl htX rfl hnn
  exact hrows G L K e t hw A hAJ hcyc hA3 htX hNO

end Two

section Main

theorem false_of_e6Work_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SLmNotOddLieInputAt 6) (hSpor : CatSLmSporadicAt 6) (hFC : E6FieldCoverInput)
    (hFam : FieldCoverFamilyInput) (h3 : E6FieldRowStep3Input) (hEnd : E6FieldEndgameEvenInput)
    (hSCT : E6SwapRowCTInput) (hSU : E6SwapRowUniqueInput) (h2p : E6TwoPositionInput)
    (h2r : E6TwoRowsInput) {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type}
    [Field K₂] [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ} (hq : QuadraticFrobenius K₂ σ f)
    (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {t : G} (hw : F4Work L (fixSubfield σ) t f) :
    False := by
  have : CharP (fixSubfield σ) 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by have := hw.one_le; omega
    exact false_of_two hGLS hXodd hSpor h2p h2r hw e
  · rcases rootFieldKind_or_rootSwapKind hGLS hXodd hSpor hw hf2 e with hk | hk
    · exact false_of_fieldRow hFC hFam h3 hEnd hq hf2 e hw hk
    · exact false_of_swapRow hSCT hSU hq hf2 e hw hk

theorem seitzExclusion_highE6_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SLmNotOddLieInputAt 6) (hSpor : CatSLmSporadicAt 6) (hFC : E6FieldCoverInput)
    (hFam : FieldCoverFamilyInput) (h3 : E6FieldRowStep3Input) (hEnd : E6FieldEndgameEvenInput)
    (hSCT : E6SwapRowCTInput) (hSU : E6SwapRowUniqueInput) (h2p : E6TwoPositionInput)
    (h2r : E6TwoRowsInput) : SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_forall fun _ _ _ _ _ _ _ _ _ _ hq e _ hw =>
    false_of_e6Work_of_inputs hGLS hXodd hSpor hFC hFam h3 hEnd hSCT hSU h2p h2r hq e hw

end Main

end CFSG.SeitzReduction.E6Pilot
