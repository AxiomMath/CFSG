module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceFrame
public import CFSG.ClassicalInvolution.Balance.WeakFrame.TwoBalanced
import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

theorem IsInvolutionMember.of_weakMember {F : Type*} [Field F] [Finite F] {G : Type*} [Group G]
    {K : Subgroup G} {z : G} (h : WeakMember F K z) (h4 : 4 ≤ Nat.card F) :
    IsInvolutionMember K := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hc := h.isCentralInvolution
  exact ⟨h.perfect.commutator_eq_top,
    Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4), z, hc.mem, hc.sq,
    hc.central, h.subnormal⟩

section WeakFrame

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem twoBalancedWrt_of_weakFrame_of_layers (Fr : WeakToralFrame F Ω E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLayersAt Ω E a) : TwoBalancedWrt E := by
  have hcomm := weak_isMulCommutative Fr.toWeakPreFrame
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hcomm ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Fr.comm ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => Fr.elem f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hloc a ha ha1 L hL with h | h | hfree
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne_weak Fr ha hF₀E h4 (Or.inl h)
    exact absurd hfc (hfaith f hf hf1)
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne_weak Fr ha hF₀E h4 (Or.inr h)
    exact absurd hfc (hfaith f hf hf1)
  · exact hfree F₀ hF₀E h4 hFn hfaith

theorem deltaCore_eq_bot_of_weakFrame_of_layers (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hloc : ∀ a ∈ E, a ≠ 1 → ComponentLayersAt Ω E a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_fusionGenerated
    ⟨weak_isMulCommutative Fr.toWeakPreFrame, fun x hx => by rw [pow_two]; exact Fr.elem x hx⟩
    h16 (twoBalancedWrt_of_weakFrame_of_layers Fr hloc) hO hGen

end WeakFrame

end CFSG.ClassicalInvolution.Balance
