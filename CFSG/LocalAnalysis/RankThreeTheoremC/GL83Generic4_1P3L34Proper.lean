module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SignalizerCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_hstarProper (hS : Setting G) {M : Subgroup G} {x : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    {U S₁ : Subgroup G} (hxU : x ∈ U) (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁)
    (hS₁M : ¬ S₁ ≤ M) (hcomm : (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) = ⁅S₁, zpowers x⁆) :
    (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) ≠ ⊥ := by
  intro hbot
  rw [hcomm] at hbot
  have hne : S₁ ≠ ⊥ := fun h => hS₁M (h ▸ bot_le)
  set H : Subgroup G := normalizer (S₁ : Set G) with hH
  have hH2 : IsTwoLocal H := ⟨S₁, hne, hS₁.1, rfl⟩
  have hxH : x ∈ H := hS₁.2.1 hxU
  have hxC : x ∈ centralizer (S₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have : s * x * s⁻¹ * x⁻¹ ∈ (⁅S₁, zpowers x⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hs (mem_zpowers x)
    rw [hbot, Subgroup.mem_bot] at this
    calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
      _ = x * s := by rw [this, one_mul]
  have hcore : pCoreOf 2 H = S₁ := by
    refine hS₁.2.2 (pCoreOf 2 H) (CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 H) ?_ ?_
    · exact hS₁.2.1.trans (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 H)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 S₁ hS₁.1
  have hxS : x ∈ S₁ := by
    have := hS.charTwo H hH2 ⟨hxH, by rw [hcore]; exact hxC⟩
    rwa [hcore] at this
  obtain ⟨k, hk⟩ := hS₁.1 ⟨x, hxS⟩
  have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have h3 : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hxk
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
