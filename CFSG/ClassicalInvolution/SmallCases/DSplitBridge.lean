module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBoot

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime]

theorem routeD_deltaConnected_of_dConnected_of_exact {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (CoreAssembly.conjClass K))
    (hex : ExactMembers (CoreAssembly.conjClass K))
    (hP1 : LocalOddCentral (CoreAssembly.conjClass K) {z}) :
    RouteD.DeltaConnected (CoreAssembly.conjClass K) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ (exists_single_class K)
    (mem_conjClass_self K) hz hP1
  have hqs : ∀ J ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple J := fun J hJ =>
    isQuasisimple_of_mem_exactMembers hq hΩ hex hJ
  exact routeD_deltaConnected_of_omegaConnected ⟨K, mem_conjClass_self K⟩
    (omegaConnected_of_tqChain hnab hΩ hIH hqs hP1all (tqChain_of_dConnected hp2 hq hz hD))

@[expose] def BootNoTripleD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ExactMembers (CoreAssembly.conjClass K) ∧ LocalOddCentral (CoreAssembly.conjClass K) {z}

theorem bootNoTriple_of_bootNoTripleD (h : BootNoTripleD p f) : BootNoTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  exact h G hnab hp2 hq K z hz hBelow
    (dConnected_of_omegaConnected (Balance.Bootstrap.omegaConnected_of_deltaConnected hconn))
    hdata hT

@[expose] def NoDataD (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass K) → ¬ BootData p f (CoreAssembly.conjClass K) →
      CFSG.ClassicalInvolution.DeltaConnected K

@[expose] def DBridge (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass K) → CFSG.ClassicalInvolution.DeltaConnected K

theorem deltaConnected_of_dConnected (hmodel : LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hexotic : ExoticLeviBlock p f)
    (hBN : BootNoTripleD p f) (hND : NoDataD p f) : DBridge p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  by_cases hT : IndepTriple p f (CoreAssembly.conjClass K)
  · obtain ⟨hex, hP1⟩ := bootTripleD hmodel hMFC hexotic G hnab hp2 hq K z hz hBelow hD hT
    exact (deltaConnected_iff K).mpr
      (routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hP1)
  · by_cases hdata : BootData p f (CoreAssembly.conjClass K)
    · obtain ⟨hex, hP1⟩ := hBN G hnab hp2 hq K z hz hBelow hD hdata hT
      exact (deltaConnected_iff K).mpr
        (routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hP1)
    · exact hND G hnab hp2 hq hBelow K z hz h3 h4 hD hdata

end CFSG.ClassicalInvolution.Disconnected
