module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleDStage
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupInputs
public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure FuzzyBalancedDataD (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  z₀A : z₀ ∈ A
  tq : A ≤ trivialOnQuot L₀
  balance : RankThreeBalance A
  frame : FrameSideTwoD p f Ω A S
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

namespace FuzzyBalancedDataD

variable {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)} {a : G}

theorem cent [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hconn : DConnected Ω)
    (h : FuzzyBalancedDataD p f Ω L₀ z₀ A S a) : L₀ ≤ Subgroup.centralizer (A : Set G) := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hgen : rankTwoSpan A = ⊤ := rankTwoSpan_eq_top_of_dConnected hp2 hq hΩ h.frame hconn
  have hc := h.cls.isCentralInvolution
  have hz2 : z₀ * z₀ = 1 := h.balance.mul_self h.z₀A
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  by_cases hgz : g = z₀
  · rw [hgz]
    exact hc.central x hx
  have hg2 : g * g = 1 := h.balance.mul_self hg
  have hcomm : z₀ * g = g * z₀ := h.balance.comm h.z₀A hg
  have hFA : Subgroup.closure ({z₀, g} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact h.z₀A
    · rw [Set.mem_singleton_iff.mp hy]
      exact hg
  have hcard : Nat.card (Subgroup.closure ({z₀, g} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hg2 hc.ne_one hg1 (fun e => hgz e.symm) hcomm
  have hF : Subgroup.closure ({z₀, g} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have hα : alphaCore (Subgroup.closure ({z₀, g} : Set G)) = ⊥ :=
    TypeCSetup.alphaCore_eq_bot_of_rankTwoSpan_eq_top hO h.balance hgen hF
  exact Theorem5.mem_centralizer_of_alphaCore_eq_bot h.cls (h.tq hg) hg2 hc.ne_one hα x hx

end FuzzyBalancedDataD

theorem exactMembers_and_localOddCentral_of_fuzzyBalancedD [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)}
    {a : G} (h : FuzzyBalancedDataD p f Ω L₀ z₀ A S a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balancedD hnab hp2 hq hΩ hsingle hIH hconn h.balance h.mem
    h.cls h.z₀A (h.cent hnab hp2 hq hΩ hconn) h.frame h.a1 h.aClassical h.cover h.nine

@[expose] def FuzzyBalancedExistsD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyBalancedDataD p f (CoreAssembly.conjClass K) L₀ z₀ A S a

theorem bootNoTripleD_of_fuzzyBalancedExistsD (h : FuzzyBalancedExistsD p f) :
    BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyBalancedD hnab hp2 hq hΩ
    (exists_single_class K) hIH hconn hgood
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

@[expose] def ExactP1D (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass K) →
      ExactMembers (CoreAssembly.conjClass K) ∧ LocalOddCentral (CoreAssembly.conjClass K) {z}

theorem dBridge_of_exactP1D (h : ExactP1D p f) : DBridge p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  obtain ⟨hex, hP1⟩ := h G hnab hp2 hq hBelow K z hz h3 h4 hD
  exact (deltaConnected_iff K).mpr
    (routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hP1)

theorem noDataD_of_exactP1D (h : ExactP1D p f) : NoDataD p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD _
  exact dBridge_of_exactP1D h G hnab hp2 hq hBelow K z hz h3 h4 hD

@[expose] def FuzzyBalancedExistsAllD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyBalancedDataD p f (CoreAssembly.conjClass K) L₀ z₀ A S a

theorem exactP1D_of_fuzzyBalancedExistsAllD (h : FuzzyBalancedExistsAllD p f) : ExactP1D p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  obtain ⟨L₀, z₀, A, S, a, hgood⟩ := h G hnab hp2 hq hBelow K z hz h3 h4 hD
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyBalancedD hnab hp2 hq hΩ
    (exists_single_class K) hIH hD hgood
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem dBridge_of_fuzzyBalancedExistsAllD (h : FuzzyBalancedExistsAllD p f) : DBridge p f :=
  dBridge_of_exactP1D (exactP1D_of_fuzzyBalancedExistsAllD h)

end CFSG.ClassicalInvolution.Disconnected
