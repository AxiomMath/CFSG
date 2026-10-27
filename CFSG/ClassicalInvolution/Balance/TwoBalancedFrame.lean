module

public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.ClassicalInvolution.Balance.OmegaFreeComponents
public import CFSG.ClassicalInvolution.Balance.Quotient
public import CFSG.ClassicalInvolution.Balance.FrameIndex

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

theorem pPrimeCore_oddQuot_eq_bot [Finite G] (a : G) : CFSG.pPrimeCore 2 (OddQuot a) = ⊥ := by
  rw [← CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
  exact OddCore.quotient_corefree _

@[expose] def ComponentBalanceAt (Ω : Set (Subgroup G)) (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ IsLocallyTwoBalanced (L ⧸ Subgroup.center L)

theorem card_modOdd_of_exponent_two [Finite G] {a : G} {F₀ : Subgroup G}
    (hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G)) (hF2 : ∀ f ∈ F₀, f * f = 1) :
    Nat.card (modOdd a F₀) = Nat.card F₀ := by
  set P : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    F₀.subgroupOf (Subgroup.centralizer ({a} : Set G)) with hP
  have hinj : Function.Injective ((oddQuotMk a).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : oddQuotMk a (x : ↥(Subgroup.centralizer ({a} : Set G))) = 1 := hx
    have hxx : (x : ↥(Subgroup.centralizer ({a} : Set G))) * x = 1 :=
      Subtype.ext (hF2 _ (Subgroup.mem_subgroupOf.mp x.2))
    exact Subtype.ext (eq_one_of_oddQuotMk_eq_one hxx hx1)
  have hrange : modOdd a F₀ = ((oddQuotMk a).comp P.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv

section Frame

variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem twoBalancedWrt_of_frame [Finite G] (Fr : ToralFrame F Ω E S)
    (hsym : PairingSymmetric E S) (hconn : PairingConnected E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a) :
    TwoBalancedWrt E := by
  have hcomm := frame_isMulCommutative Fr
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hcomm ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (frame_comm Fr ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => Fr.elem f (hF₀E hf)
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_locallyTwoBalanced (pPrimeCore_oddQuot_eq_bot a) ?_ ?_ ?_
  · rw [card_modOdd_of_exponent_two hFC hF2, h4]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  · intro L hL _ hfaith
    rcases hloc a ha ha1 L hL with h | h | h
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne Fr hsym hconn ha hF₀E h4
          (Or.inl h)
      exact absurd hfc (hfaith f hf hf1)
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne Fr hsym hconn ha hF₀E h4
          (Or.inr h)
      exact absurd hfc (hfaith f hf hf1)
    · exact h

theorem twoBalancedWrt_of_frame_of_a2Dichotomy [Finite G] (Fr : ToralFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) (hnc : NonCommConnected S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a) :
    TwoBalancedWrt E :=
  twoBalancedWrt_of_frame Fr (pairingSymmetric_of_a2Dichotomy Fr hA2)
    (pairingConnected_of_nonCommConnected Fr hA2 hfib hnc) hloc

end Frame

section Triviality

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem deltaCore_eq_bot_of_frame (Fr : ToralFrame F Ω E S) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) (h16 : 16 ≤ Nat.card E)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_fusionGenerated
    ⟨frame_isMulCommutative Fr, fun x hx => by rw [pow_two]; exact Fr.elem x hx⟩ h16
    (twoBalancedWrt_of_frame Fr hsym hconn hloc) hO hGen

end Triviality

end CFSG.ClassicalInvolution.Balance
