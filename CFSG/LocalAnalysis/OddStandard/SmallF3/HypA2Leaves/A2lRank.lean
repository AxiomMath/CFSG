module

public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift

theorem a2l_exists_central_involution {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 2 ↥(center K)) (hc : center K ≠ ⊥) :
    ∃ z : K, z ∈ center K ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥(center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hc
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hdvd : 2 ∣ Nat.card ↥(center K) := by
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd hk Finite.one_lt_card.ne'
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨z, z.2, ?_, ?_⟩
  · intro e1
    rw [← Subgroup.orderOf_coe, e1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [← Subgroup.orderOf_coe] at hz
    rw [← hz]
    exact pow_orderOf_eq_one _

theorem a2l_two_le_pRank_of_center_bot {K : Type} [Group K]
    [Finite K] (hK : CFSG.IsQuasisimple K) (hc : center K = ⊥) : 2 ≤ CFSG.pRank 2 K := by
  let e : K ⧸ center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup K := (e.isSimpleGroup_congr).1 hK.2.1
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  obtain ⟨V, -, hV2, hV4⟩ := RankThree.OddKernel.exists_four_group_of_isSimpleGroup hnab
  exact GH74.GLS.IVK.Lifted.le_pRank_two_of_elementaryAbelian V
    (GH74.GLS.IVK.Lifted.isElementaryAbelian_two_of_sq_eq_one hV2) (k := 2) (by rw [hV4]; norm_num)

theorem a2l_four_le_pRank_of_e8Datum {K X : Type} [Group K] [Finite K] [Group X]
    {a₁ a₂ a₃ n : X} (h : E8Datum a₁ a₂ a₃ n) (e : K ⧸ center K ≃* X) {z : K}
    (hzc : z ∈ center K) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) : 4 ≤ CFSG.pRank 2 K := by
  set φ : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center K)) with hφdef
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center K := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (center K)) x = 1 := e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).mp hx'
  have hzk : φ z = 1 := by
    change e (QuotientGroup.mk (z : K)) = 1
    rw [(QuotientGroup.eq_one_iff (z : K)).mpr hzc, map_one]
  exact h.four_le_pRank hφ hker hzk hz1 hz2

end CFSG.OddStandard.SmallF3.HypA2Leaves
