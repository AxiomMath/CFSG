module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedRange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowRange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPerfect

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphTwistedMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Inputs

@[expose] def TwistedE6GraphRowDInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N₁ N₂ : AmalgamNeighbour, (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X) →
    HR8Kind e t f N₁ .unitary6 → HR8Kind e t f N₂ .omegaMinus8 →
    ∀ e₁ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₁ N₁ →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      ΦX.range = neighbourCore e N₁ →
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) →
      IsLeviNormalizedU h ε e₁ ΦX →
    ∃ ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G,
      ΦY.range = neighbourCore e N₂ ∧
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦY x * t⁻¹ = ΦY y) ∧
      ((∀ x : twLevi F h.barEquiv.toRingHom {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
          twLeviRestrict ΦY one_two_subset_Y x) ∨
        (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y)) ∧
      ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)

end Inputs

section Orientation

theorem exists_orientation_of_twistedE6RowKinds {G : Type} [Group G] {L : Subgroup G} {K : Type}
    [Field K] {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ} (hk : TwistedE6RowKinds e t f) :
    ∃ N₁ N₂ : AmalgamNeighbour, ((N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X)) ∧
      HR8Kind e t f N₁ .unitary6 ∧ HR8Kind e t f N₂ .omegaMinus8 := by
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨.X, .Y, .inl ⟨rfl, rfl⟩, h1, h2⟩
  · exact ⟨.Y, .X, .inr ⟨rfl, rfl⟩, h2, h1⟩

end Orientation

section Param

theorem twistedE6GraphRowParamInput_of_dInput (hD : TwistedE6GraphRowDInput) :
    TwistedE6GraphRowParamInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨N₁, N₂, hN, h6, h8⟩ := exists_orientation_of_twistedE6RowKinds hk
  have hN₁ : N₁ = .X ∨ N₁ = .Y := by
    rcases hN with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  have hN₂ : N₂ = .X ∨ N₂ = .Y := by
    rcases hN with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inr rfl
    · exact .inl rfl
  obtain ⟨F, iF, iF2, iF3, h, ε, e₁, ΦX, hfr, hr, hker, hc, hn⟩ :=
    exists_twParamX_normalized hw hf e hN₁ h6
  obtain ⟨ΦY, hrY, hcY, htw, hcomm⟩ :=
    hD G L K e t f hw hf N₁ N₂ hN h6 h8 e₁ hfr F h ε ΦX hr hker hc hn
  obtain ⟨t₀, ht₀θ, ht₀⟩ := exists_barFixed_unit_sq_ne_one h hf
  have hθ : ∀ c, h.barEquiv.toRingHom (h.barEquiv.toRingHom c) = c := h.bar_bar
  have hP12 := commutator_twLevi_one_two h.barEquiv.toRingHom hθ ht₀θ ht₀
  have hP0 := commutator_twLevi_zero h.barEquiv.toRingHom hθ ht₀θ ht₀
  obtain ⟨hM1, hM2⟩ := range_twLeviRestrict_le_pieceCore e hN hr hrY htw hP12
  have hE₁ := neighbourCore_le_pieceSpan_of_twParamX hq e hr hn
    (hM1.trans (pieceCore_one_two_le_pieceSpan e))
  have hE₂ := neighbourCore_le_pieceSpan_of_twParamY hw hf e hN₂ hrY hcY hP0
    (hM2.trans (pieceCore_one_two_le_pieceSpan e))
  have hXY : neighbourCore e .X ≤ pieceSpan e ∧ neighbourCore e .Y ≤ pieceSpan e := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hE₁, hE₂⟩
    · exact ⟨hE₂, hE₁⟩
  exact ⟨F, iF, iF2, h.barEquiv, unitaryFieldData_card_sq h, fun c => rfl, ΦX, ΦY,
    isTwistedE6GraphRowParam_of_neighbourCore' hq htw hc hcY hcomm hN hr hrY hXY.1 hXY.2⟩

theorem twistedE6RowCTQuotInput_of_dInput (hD : TwistedE6GraphRowDInput) :
    TwistedE6RowCTQuotInput :=
  twistedE6RowCTQuotInput_of_paramInput (twistedE6GraphRowParamInput_of_dInput hD)

end Param

end CFSG.SeitzReduction.F4Pilot
