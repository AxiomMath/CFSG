module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphTwistedDMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Inputs

@[expose] def TwistedE6GraphRowLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) (hw : F4Work L K t f) (hf : 2 ≤ f),
    ∀ N₁ N₂ : AmalgamNeighbour, (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X) →
    HR8Kind e t f N₁ .unitary6 → HR8Kind e t f N₂ .omegaMinus8 →
    ∀ e₁ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₁ N₁ →
    ∀ e₂ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₂ N₂ →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      ΦX.range = neighbourCore e N₁ →
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) →
      IsLeviNormalizedU h ε e₁ ΦX →
    ∀ (c : K) (hc : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0)
      (Θ : StatedOmega (StatedQuadMinus 4 K 1 c) ≃*
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes),
      (∀ g, ((Θ (omegaMinusBetaC K 1 c g) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom (Θ g)) →
    ∃ (ε' : K ≃+* K) (s₀ : StatedSp 3 K),
      ∀ ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G,
      ΦY.range = neighbourCore e N₂ → Function.Injective ΦY →
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦY x * t⁻¹ = ΦY y) →
      (∀ s, ΦY (Θ (omegaMinusIota hw.card_eq hf hc s)) = levi6Hom e₂ ε' (s₀ * s * s₀⁻¹)) →
      ((∀ x : twLevi F h.barEquiv.toRingHom {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
          twLeviRestrict ΦY one_two_subset_Y x) ∨
        (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y)) ∧
      ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)

@[expose] def TwistedE6GraphRowModelLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) (hw : F4Work L K t f) (hf : 2 ≤ f),
    ∀ N₁ N₂ : AmalgamNeighbour, (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X) →
    HR8Kind e t f N₁ .unitary6 → HR8Kind e t f N₂ .omegaMinus8 →
    ∀ e₁ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₁ N₁ →
    ∀ e₂ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₂ N₂ →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      ΦX.range = neighbourCore e N₁ →
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) →
      IsLeviNormalizedU h ε e₁ ΦX →
    ∃ (c : K) (hc : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0)
      (Θ : StatedOmega (StatedQuadMinus 4 K 1 c) ≃*
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes),
      (∀ g, ((Θ (omegaMinusBetaC K 1 c g) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom (Θ g)) ∧
    ∃ (ε' : K ≃+* K) (s₀ : StatedSp 3 K),
      ∀ ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G,
      ΦY.range = neighbourCore e N₂ → Function.Injective ΦY →
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦY x * t⁻¹ = ΦY y) →
      (∀ s, ΦY (Θ (omegaMinusIota hw.card_eq hf hc s)) = levi6Hom e₂ ε' (s₀ * s * s₀⁻¹)) →
      ((∀ x : twLevi F h.barEquiv.toRingHom {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
          twLeviRestrict ΦY one_two_subset_Y x) ∨
        (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y)) ∧
      ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)

end Inputs

theorem exists_isNeighbourFrame_of_ne {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour}
    (hN : N ≠ .X') : ∃ e₂ : L ≃* adjointGroup .F4 K, IsNeighbourFrame e e₂ N := by
  cases N with
  | X => exact ⟨e, rfl⟩
  | Y =>
    have hc : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    exact ⟨e.trans (graphAutF4 K).symm, hc, rfl⟩
  | X' => exact absurd rfl hN

section Reduction

theorem exists_twD_param_of_cover {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 f F}
    {t : G} {E : Subgroup G} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {c : K}
    (hcirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0)
    (Θ : StatedOmega (StatedQuadMinus 4 K 1 c) ≃*
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes)
    (hΘ : ∀ g, ((Θ (omegaMinusBetaC K 1 c g) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom (Θ g))
    (s₀ : StatedSp 3 K) {lam : StatedSp 3 K →* G}
    {Φ : StatedOmega (StatedQuadMinus 4 K 1 c) →* G} (hi : Function.Injective Φ)
    (hrΦ : Φ.range = E) (ht : ∀ g, t * Φ g * t⁻¹ = Φ (omegaMinusBetaC K 1 c g))
    (hnΦ : ∀ s, Φ (omegaMinusIota hK hf hcirr s) = lam s) :
    ∃ ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G,
      Function.Injective ΦY ∧ ΦY.range = E ∧
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦY x * t⁻¹ = ΦY y) ∧
      ∀ s, ΦY (Θ (omegaMinusIota hK hf hcirr s)) = lam (s₀ * s * s₀⁻¹) := by
  obtain ⟨u, hu⟩ : ∃ u, u = omegaMinusIota hK hf hcirr s₀ := ⟨_, rfl⟩
  have hus : omegaMinusBetaC K 1 c u = u := by
    have hs : u ∈ fixedSubgroup (omegaMinusBetaC K 1 c) :=
      (range_omegaMinusIota hK hf hcirr) ▸ ⟨s₀, hu.symm⟩
    exact hs
  refine ⟨(Φ.comp (MulAut.conj u).toMonoidHom).comp Θ.symm.toMonoidHom,
    (hi.comp (MulAut.conj u).injective).comp Θ.symm.injective, ?_, fun x y hxy => ?_,
    fun s => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.symm.surjective,
      ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulAut.conj u).surjective, ← MonoidHom.range_eq_map, hrΦ]
  · have hy : Θ.symm y = omegaMinusBetaC K 1 c (Θ.symm x) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hxy, hΘ, MulEquiv.apply_symm_apply]
    change t * Φ (u * Θ.symm x * u⁻¹) * t⁻¹ = Φ (u * Θ.symm y * u⁻¹)
    rw [hy, ht]
    congr 1
    rw [map_mul (omegaMinusBetaC K 1 c), map_mul (omegaMinusBetaC K 1 c),
      map_inv (omegaMinusBetaC K 1 c), hus]
  · change Φ (u * Θ.symm (Θ (omegaMinusIota hK hf hcirr s)) * u⁻¹) = _
    rw [MulEquiv.symm_apply_apply, hu, ← map_inv, ← map_mul, ← map_mul, hnΦ]

theorem twistedE6GraphRowDInput_of_modelLeviInput (hML : TwistedE6GraphRowModelLeviInput) :
    TwistedE6GraphRowDInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ F _ _ _ h ε ΦX hr hker hc hn
  have hN₂ : N₂ ≠ .X' := by
    rcases hN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨e₂, he₂⟩ := exists_isNeighbourFrame_of_ne e hN₂
  obtain ⟨c, hcirr, Θ, hΘ, ε', s₀, H⟩ :=
    hML G L K e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ F h ε ΦX hr hker hc hn
  obtain ⟨Φ, hi, hrΦ, ht, hnΦ⟩ :=
    exists_omegaMinus_cover_normalized hw hf e he₂ h8 hw.card_eq hcirr ε'
  obtain ⟨ΦY, hiY, hrY, hcY, hnY⟩ :=
    exists_twD_param_of_cover hw.card_eq hf hcirr Θ hΘ s₀ hi hrΦ ht hnΦ
  have H1 := H ΦY hrY hiY hcY
  have hnY' : ∀ s, ΦY (Θ (omegaMinusIota hw.card_eq hf hcirr s)) =
      levi6Hom e₂ ε' (s₀ * s * s₀⁻¹) := hnY
  refine ⟨ΦY, hrY, hcY, ?_⟩
  have H2 := H1 hnY'
  refine ⟨?_, ?_⟩
  · rcases H2.1 with h1 | h1
    · left
      intro x
      exact h1 x
    · right
      intro x y hxy
      exact h1 x y hxy
  · exact H2.2

end Reduction

end CFSG.SeitzReduction.F4Pilot
