module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def FourteenFifteenNormAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H → E ≤ kSub q M H →
    (∀ H₁ ∈ H2StarFam M E, kSub q M H ≤ kSub q M H₁ → kSub q M H₁ = kSub q M H) →
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M) →
      Subgroup.normalizer (T : Set G) ≤ H

@[expose] def KNormalAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H →
    H ≤ Subgroup.normalizer (kSub q M H : Set G)

@[expose] def KSylowTwoNotLeAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (kSub q M H) → ¬ S ≤ M

namespace HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem not_isSylowOf (hK : KNormalAt M) (hS : KSylowTwoNotLeAt M)
    (h : HypCGen G M q E H) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hTH
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kSub q M H) (kSub q M H) :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hTH (kSub_le q M H) (hK q E H h)
  exact hS q E H h (T ⊓ kSub q M H) hTK
    (le_trans inf_le_left (hT.le.trans inf_le_right))

end HypCGen

variable {M : Subgroup G}

theorem fourteenFifteenTwoAt_of (hN : FourteenFifteenNormAt M) (hK : KNormalAt M)
    (hS : KSylowTwoNotLeAt M) : FourteenFifteenTwoAt M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q E H hdata hEK hmax T hT
  refine ⟨?_, HypCGen.not_isSylowOf hK hS hdata hT⟩
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT
    (le_trans inf_le_left (hN q E H hdata hEK hmax T hT))

theorem agl81FourteenFifteen_of_parts
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        FourteenFifteenOneAt M ∧ FourteenFifteenNormAt M ∧ KNormalAt M ∧ KSylowTwoNotLeAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_one_two ?_
  intro G _ _ hC M hM hσ
  obtain ⟨h1, hN, hK, hS⟩ := h G hC M hM hσ
  exact ⟨h1, fourteenFifteenTwoAt_of hN hK hS⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
