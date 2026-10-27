module

public import CFSG.ClassicalInvolution.Q3.ExactDelta
public import CFSG.ClassicalInvolution.Q3.LocalOddCentral
public import CFSG.ClassicalInvolution.Q3.TripleBalance
public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem group_le_centralizingLayer_of_exactTriple {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {b : G}
    (hb : b ∈ T.group) : T.group ≤ centralizingLayer Ω {b} := by
  have hbK : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({b} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have h1 : K₁ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₁, hbK T.le_centralizer₁⟩
  have h2 : K₂ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₂, hbK T.le_centralizer₂⟩
  have h3 : K₃ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₃, hbK T.le_centralizer₃⟩
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [h1 T.mem₁, h2 T.mem₂, h3 T.mem₃]

theorem rankThreeBalance3 (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    (hAY : ∀ b ∈ A, b ≠ 1 → A ≤ centralizingLayer Ω {b})
    (hnc : ∀ b ∈ A, b ≠ 1 → b ∉ Subgroup.center G) (h2 : TwoBalancedWrt A) :
    RankThreeBalance A :=
  ⟨hA, hcard, weakBalanced_of_localOddCentralizer3 hΩ hO hA hAY hnc, h2⟩

theorem stage2_of_rankThreeBalance3 (hOG : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω) {A : Subgroup G} (hA : RankThreeBalance A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤)
    (hnc : ∀ b ∈ A, b ≠ 1 → b ∉ Subgroup.center G) {𝒦 : Set (Subgroup G)}
    (h𝒦 : ∀ K ∈ 𝒦, K ∈ Ω ∧ ∃ z ∈ A, IsClassicalMember3 K z ∧
      K ≤ Subgroup.centralizer (A : Set G)) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧ StronglyBalanced A ∧
      ∀ K ∈ 𝒦, classicalInvolutionOddCore ↥K = ⊥ := by
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA hOG hgen
  refine ⟨hΔ, stronglyBalanced_of_weakBalanced hA.elem (by rw [hA.card]) hA.weak hΔ, ?_⟩
  intro K hK
  obtain ⟨hKΩ, z, hzA, hz, hKA⟩ := h𝒦 K hK
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two A hA.elem (by rw [hA.card]; norm_num)
  exact classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ hIH hKΩ hz
    (hKA.trans (Subgroup.centralizer_le hF₀.1))
    (fun f hf hf1 => hnc f (hF₀.1 hf) hf1) (hΔ F₀ hF₀)

theorem stage2_of_exactTriple3 (hOG : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (h2 : TwoBalancedWrt T.group)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧ StronglyBalanced T.group ∧
      classicalInvolutionOddCore ↥K₁ = ⊥ ∧ classicalInvolutionOddCore ↥K₂ = ⊥ ∧
      classicalInvolutionOddCore ↥K₃ = ⊥ := by
  have hA := rankThreeBalance3 hΩ hO T.isElemAbelian (T.card_eq_eight hind)
    (fun b hb _ => group_le_centralizingLayer_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ hb) hnc h2
  have hmem : T.group ≤ T.group := le_rfl
  obtain ⟨hΔ, hSB, hex⟩ := stage2_of_rankThreeBalance3 hOG hΩ hIH hA hgen hnc
    (𝒦 := {K₁, K₂, K₃}) (by
      intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl | rfl
      · exact ⟨hΩ₁, z₁, Subgroup.subset_closure (by simp), hz₁, T.le_centralizer₁⟩
      · exact ⟨hΩ₂, z₂, Subgroup.subset_closure (by simp), hz₂, T.le_centralizer₂⟩
      · exact ⟨hΩ₃, z₃, Subgroup.subset_closure (by simp), hz₃, T.le_centralizer₃⟩)
  exact ⟨hΔ, hSB, hex K₁ (by simp), hex K₂ (by simp), hex K₃ (by simp)⟩

theorem covered_of_le_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer (A : Set G)) :
    ∃ F ∈ signalizerFunctorEk 2 2 A, x ∈ F ∧ L ≤ Subgroup.centralizer (F : Set G) := by
  obtain ⟨F, hF, hxF⟩ := exists_mem_signalizerFunctorEk_of_mem hA h8 hx hx1
  exact ⟨F, hF, hxF, hL.trans (Subgroup.centralizer_le hF.1)⟩

theorem localOddCentral3_of_exactTriple (hOG : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (h2 : TwoBalancedWrt T.group)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤)
    {x : G} (hx : x ∈ T.group) (hx1 : x ≠ 1)
    (hcov : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) →
      ∃ F ∈ signalizerFunctorEk 2 2 T.group, x ∈ F ∧ L ≤ Subgroup.centralizer (F : Set G)) :
    LocalOddCentral Ω {x} := by
  have hAY : ∀ b ∈ T.group, b ≠ 1 → T.group ≤ centralizingLayer Ω {b} := fun b hb _ =>
    group_le_centralizingLayer_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ hb
  obtain ⟨hΔ, hSB, -⟩ := stage2_of_exactTriple3 hOG hΩ hIH hO T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
    hnc h2 hgen
  exact localOddCentral3_of_covered hΩ hO T.isElemAbelian hAY hnc hSB hΔ hx hx1 hcov

theorem stage2_of_exactTriple3_of_balance (hOG : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentBalanceAt Ω a)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧ StronglyBalanced T.group ∧
      classicalInvolutionOddCore ↥K₁ = ⊥ ∧ classicalInvolutionOddCore ↥K₂ = ⊥ ∧
      classicalInvolutionOddCore ↥K₃ = ⊥ :=
  stage2_of_exactTriple3 hOG hΩ hIH hO T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hnc
    (twoBalancedWrt_of_exactTriple_of_balance T hΩ₁ hΩ₂ hΩ₃ hloc) hgen

theorem localOddCentral3_of_exactTriple_of_balance
    (hOG : CFSG.Open.componentClassificationOddCore G = ⊥)
    (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω) (hO : LocalOddCentralizer3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hnc : ∀ b ∈ T.group, b ≠ 1 → b ∉ Subgroup.center G)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentBalanceAt Ω a)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤)
    {x : G} (hx : x ∈ T.group) (hx1 : x ≠ 1)
    (hcov : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) →
      ∃ F ∈ signalizerFunctorEk 2 2 T.group, x ∈ F ∧ L ≤ Subgroup.centralizer (F : Set G)) :
    LocalOddCentral Ω {x} :=
  localOddCentral3_of_exactTriple hOG hΩ hIH hO T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hnc
    (twoBalancedWrt_of_exactTriple_of_balance T hΩ₁ hΩ₂ hΩ₃ hloc) hgen hx hx1 hcov

end CFSG.ClassicalInvolution.Q3
