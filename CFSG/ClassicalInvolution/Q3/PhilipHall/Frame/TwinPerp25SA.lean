module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

theorem a4_of_centExt (hExt : P25_CentExt) : P25_A4 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨hzA, hz2, hz1⟩ := z_facts hyp
  by_cases hA : cA S R R' = Subgroup.zpowers z
  · have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    change Nat.card ↥(cA S R R') ≤ 4
    rw [hA, Nat.card_zpowers, hz2']
    norm_num
  · obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := exists_normal_four_bad hyp hA
    have hA0 := fourExhausts_of_centExt hExt (hyp := hyp) haA ha2 ha1 haz hconj hbad
    have haz' : a * z = z * a := hyp.hzS a haA.1
    have hAeq : Subgroup.closure ({a, z} : Set G) = cA S R R' := by
      refine le_antisymm ?_ fun b hb =>
        (inFour_iff_mem_closure ha2 hz2 haz').mp (hA0 b hb)
      rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact haA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hzA
    have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz haz'
    change Nat.card ↥(cA S R R') ≤ 4
    rw [← hAeq, hE.1]
    norm_num

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S
