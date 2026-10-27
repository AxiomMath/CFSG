module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceLie
public import CFSG.ClassicalInvolution.Balance.ToralBalanceWeakFrame
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.Assembly.LowTwoRank

@[expose] def IsOddLieComponent {X : Type} [Group X] (L : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ (t = .PSL → 3 ≤ n) ∧
    (t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags) ∧
    LieModel (↥L ⧸ Subgroup.center ↥L) t n p f

theorem involutionCentralizerB_of_isOddLieComponent {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hL : CFSG.Open.IsQuasisimple ↥L) (h : IsOddLieComponent L) :
    InvolutionCentralizerB L := by
  obtain ⟨t, n, p, f, hp, hn, ht, hmodel⟩ := h
  exact involutionCentralizerB_of_lieModel hL hp hn ht hmodel

theorem isOddLieComponent_of_surjective {X : Type} [Group X] {L : Subgroup X} {K : Type}
    [Group K] (hK : CFSG.Open.IsQuasisimple K) (ψ : K →* ↥L) (hψ : Function.Surjective ψ)
    (hψ1 : ∃ x, ψ x ≠ 1) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2) (hn : t = .PSL → 3 ≤ n)
    (ht : t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags)
    (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) : IsOddLieComponent L := by
  have hK' : CFSG.IsQuasisimple K := CatalogueBAlternating.quasisimple_iff_native.mpr hK
  exact ⟨t, n, p, f, hp, hn, ht, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK' hψ
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK' hψ1)) hmodel⟩

section Frame

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

variable (Ω E) in
@[expose] def ComponentLieAt (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨
      (IsOddLieComponent L ∧ ∀ F₀ : Subgroup G, F₀ ≤ E → Nat.card F₀ = 4 →
        modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) →
        (∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
          OddCentralizerFreeMembers (modOdd a F₀) L)

theorem ComponentLieAt.componentLayersAt {a : G} (hE2 : ∀ x ∈ E, x * x = 1)
    (h : ComponentLieAt Ω E a) : ComponentLayersAt Ω E a := by
  intro L hL
  rcases h L hL with h | h | ⟨hlie, hmem⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr fun F₀ hF₀E h4 hFn hfaith => ?_)
    have hB := involutionCentralizerB_of_isOddLieComponent
      ((CFSG.isComponent_iff_open L).mp hL).2.2 hlie
    have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (hE2 _ (hF₀E hx))
      rw [this, map_one]
    exact OddCentralizerFree.of_members l2PrimeBalance hL
      (fun f hf hf1 => hB f hf1 (hF2bar f hf) (hFn hf)) (hmem F₀ hF₀E h4 hFn hfaith)

theorem ComponentLieAt.of_frameGenerated (Fr : ToralFrame F Ω E S) {a : G} (ha : a ∈ E)
    (hS : ∀ K ∈ S, IsInvolutionMember K)
    (h : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (FrameGeneratedAt E S a L ∧ IsOddLieComponent L)) :
    ComponentLieAt Ω E a := by
  intro L hL
  rcases h L hL with h | h | ⟨hgen, hlie⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hlie, fun F₀ hF₀E h4 _ _ =>
      hgen.oddCentralizerFreeMembers Fr ha hS hF₀E h4⟩)

theorem twoBalancedWrt_of_frame_of_lieComponents (Fr : ToralFrame F Ω E S)
    (hsym : PairingSymmetric E S) (hconn : PairingConnected E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLieAt Ω E a) : TwoBalancedWrt E :=
  twoBalancedWrt_of_frame_of_layers Fr hsym hconn
    fun a ha ha1 => (hloc a ha ha1).componentLayersAt Fr.elem

theorem twoBalancedWrt_of_frame_of_frameGenerated (Fr : ToralFrame F Ω E S)
    (hsym : PairingSymmetric E S) (hconn : PairingConnected E S)
    (hS : ∀ K ∈ S, IsInvolutionMember K)
    (hloc : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (FrameGeneratedAt E S a L ∧ IsOddLieComponent L)) :
    TwoBalancedWrt E :=
  twoBalancedWrt_of_frame_of_lieComponents Fr hsym hconn fun a ha ha1 =>
    ComponentLieAt.of_frameGenerated Fr ha hS (hloc a ha ha1)

theorem deltaCore_eq_bot_of_frame_of_lieComponents (Fr : ToralFrame F Ω E S)
    (hsym : PairingSymmetric E S) (hconn : PairingConnected E S) (h16 : 16 ≤ Nat.card E)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLieAt Ω E a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_frame_of_layers Fr hsym hconn h16
    (fun a ha ha1 => (hloc a ha ha1).componentLayersAt Fr.elem) hO hGen

end Frame

section WeakFrame

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem twoBalancedWrt_of_weakFrame_of_lieComponents (Fr : WeakToralFrame F Ω E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLieAt Ω E a) : TwoBalancedWrt E :=
  twoBalancedWrt_of_weakFrame_of_layers Fr fun a ha ha1 =>
    (hloc a ha ha1).componentLayersAt Fr.elem

theorem deltaCore_eq_bot_of_weakFrame_of_lieComponents (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLieAt Ω E a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_weakFrame_of_layers Fr h16
    (fun a ha ha1 => (hloc a ha ha1).componentLayersAt Fr.elem) hO hGen

end WeakFrame

end CFSG.ClassicalInvolution.Balance
