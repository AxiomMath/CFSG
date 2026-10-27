module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Tools
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2 (TypU)

theorem a2l_typU_of_chev3_even {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (h2 : 2 ∣ Nat.card K) (hS : HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K))
    (hI : ¬ GH74.GLS.InChev2 (K ⧸ center K)) : TypU K := by
  have hZs : Open.fusionZStar K = center K :=
    HarrisLit.T1.P54.fusionZStar_eq_center_of_isQuasisimple hq h2
  let e : K ⧸ Open.fusionZStar K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hZs
  refine Or.inr (Or.inl ⟨3, Nat.prime_three, by norm_num, ?_, ?_⟩)
  · exact (HypA2.isSimpleChevalleyOver_congr 3 e).2 hS
  · rw [HypA2.inChev2_congr e]
    exact hI

theorem a2l_two_dvd_card_of_involution {G : Type} [Group G] [Finite G] (T : Subgroup G) {z : G}
    (hz : z ∈ T) (hz2 : z * z = 1) (hz1 : z ≠ 1) : 2 ∣ Nat.card T := by
  have h : (⟨z, hz⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hz2)
  have h1 : (⟨z, hz⟩ : T) ≠ 1 := fun h' => hz1 (congrArg Subtype.val h')
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf (⟨z, hz⟩ : T) = 2 := orderOf_eq_prime h h1
  rw [← ho]
  exact orderOf_dvd_natCard _

end CFSG.OddStandard.SmallF3.HypA2Leaves
