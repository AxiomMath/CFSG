module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCFacts
public import CFSG.Sporadic.Th.Max3.AllConjFinal

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeC

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

section Th

theorem q_zero_facts :
    q 0 ≠ 1 ∧ q 0 ≠ z := by
  have hv : (1 : ZMod 2).val = 1 := rfl
  have h0 : nf 0 0 = 1 := by simp [nf]
  have h1 : nf 1 0 = z := by simp [nf, hv]
  have h2 : nf 0 ![1, 0, 0, 0, 0, 0, 0, 0] = q 0 := by
    simp [nf, List.ofFn_succ, hv]
  constructor
  · intro h
    have := nf_injective (a₁ := (0, ![1, 0, 0, 0, 0, 0, 0, 0])) (a₂ := (0, 0))
      (by simp only [h2, h0, h])
    have := congrArg (fun p => p.2 0) this
    simp at this
  · intro h
    have := nf_injective (a₁ := (0, ![1, 0, 0, 0, 0, 0, 0, 0])) (a₂ := (1, 0))
      (by simp only [h2, h1, h])
    have := congrArg Prod.fst this
    simp at this

theorem noOddSections_M :
    NoOddSections ↥M := by
  obtain ⟨⟨κ, -⟩, -, -, -, hC⟩ := max3_alternating_quotient
  have hQp : IsPGroup 2 ↥(Q.subgroupOf M) := by
    refine IsPGroup.of_card (n := 9) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_M).toEquiv, card_Q]
    norm_num
  refine noOddSections_of_alternating normal_Q_subgroupOf_M hQp ?_ κ
  intro m hm
  rw [Subgroup.mem_centralizer_iff] at hm
  have hmc : (m : J) ∈ Subgroup.centralizer (Q : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := hm ⟨g, Q_le_M hg⟩ (Subgroup.mem_subgroupOf.2 hg)
    have h2 := congrArg (fun y : ↥M => (y : J)) h1
    simpa using h2
  have hz : (m : J) ∈ Subgroup.zpowers z := by
    rw [← hC]
    exact ⟨hmc, m.2⟩
  exact Subgroup.mem_subgroupOf.2 ((Subgroup.zpowers_le.2 z_mem_Q) hz)

theorem involutionFacts_J :
    InvolutionFacts ↥J 92897280 := by
  have hconj : ∀ u : ↥J, orderOf u = 2 → IsConj a u := all_involutions_conjugate
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact z_mul_self) z_ne_one
  refine ⟨fun u hu => ?_, fun t u ht hu => ?_, ⟨z, q 0, hz2, ?_, z_mul_q 0, ?_⟩, a, ?_, ?_⟩
  · rw [← TabMSeven.card_centralizer_eq_of_isConj (hconj u hu),
      Kernel.centralizer_a_eq_M th_kernel_facts, card_M]
  · exact isConj_iff.1 ((hconj u hu).symm.trans (hconj t ht))
  · exact orderOf_eq_prime (by rw [sq]; exact q_mul_self 0) q_zero_facts.1
  · exact fun h => q_zero_facts.2 h.symm
  · rw [← z_eq_a]
    exact hz2
  · rw [Kernel.centralizer_a_eq_M th_kernel_facts]
    exact noOddSections_M

theorem involutionFacts_Th :
    InvolutionFacts CFSG.Blueprint.NativeSporadic.Th 92897280 := by
  have e : ↥J ≃* CFSG.Blueprint.NativeSporadic.Th := thEquivJ.symm
  exact @InvolutionFacts.of_equiv ↥J CFSG.Blueprint.NativeSporadic.Th inferInstance inferInstance
    e 92897280 involutionFacts_J

end Th

end CFSG.HardMathSupport.Dickson.I271.TabMThreeC
