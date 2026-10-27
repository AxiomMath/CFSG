module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

theorem invariant_set_transitive_of_point_stabilizer
    (N : Subgroup G) (Delta : Set Ω) (alpha : Ω) (halpha : alpha ∈ Delta)
    (hpreserve : ∀ n : G, n ∈ N → ∀ a : Ω, a ∈ Delta → rightAct a n ∈ Delta)
    (hpoint : ∀ a b : Ω, a ∈ Delta → b ∈ Delta → a ≠ alpha → b ≠ alpha →
      ∃ n : G, n ∈ N ⊓ rightStabilizer alpha ∧ rightAct a n = b)
    (hescape : ¬ N ≤ rightStabilizer alpha) :
    ∀ a b : Ω, a ∈ Delta → b ∈ Delta → ∃ n : G, n ∈ N ∧ rightAct a n = b := by
  have hmove : ∃ n : G, n ∈ N ∧ rightAct alpha n ≠ alpha := by
    by_contra hnone
    apply hescape
    intro n hn
    apply (mem_rightStabilizer alpha n).mpr
    by_contra hne
    exact hnone ⟨n, hn, hne⟩
  obtain ⟨g, hg, hgalpha⟩ := hmove
  have hbase : ∀ b : Ω, b ∈ Delta → ∃ n : G, n ∈ N ∧ rightAct alpha n = b := by
    intro b hb
    by_cases hbeq : b = alpha
    · subst b
      exact ⟨1, N.one_mem, rightAct_one alpha⟩
    · obtain ⟨k, hk, hgk⟩ := hpoint (rightAct alpha g) b
        (hpreserve g hg alpha halpha) hb hgalpha hbeq
      exact ⟨g * k, N.mul_mem hg hk.1, (rightAct_mul alpha g k).symm.trans hgk⟩
  intro a b ha hb
  obtain ⟨na, hna, halphaa⟩ := hbase a ha
  obtain ⟨nb, hnb, halphab⟩ := hbase b hb
  refine ⟨na⁻¹ * nb, N.mul_mem (N.inv_mem hna) hnb, ?_⟩
  rw [← halphaa, rightAct_mul]
  simp only [mul_inv_cancel_left]
  exact halphab

theorem invariant_set_doubly_transitive_of_point_stabilizer
    (N : Subgroup G) (Delta : Set Ω) (alpha : Ω) (halpha : alpha ∈ Delta)
    (hpreserve : ∀ n : G, n ∈ N → ∀ a : Ω, a ∈ Delta → rightAct a n ∈ Delta)
    (hpoint : ∀ a b : Ω, a ∈ Delta → b ∈ Delta → a ≠ alpha → b ≠ alpha →
      ∃ n : G, n ∈ N ⊓ rightStabilizer alpha ∧ rightAct a n = b)
    (hescape : ¬ N ≤ rightStabilizer alpha) :
    ∀ a b c d : Ω, a ∈ Delta → b ∈ Delta → c ∈ Delta → d ∈ Delta →
      a ≠ b → c ≠ d →
      ∃ n : G, n ∈ N ∧ rightAct a n = c ∧ rightAct b n = d := by
  have ht := invariant_set_transitive_of_point_stabilizer N Delta alpha halpha
    hpreserve hpoint hescape
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨x, hx, hxa⟩ := ht a alpha ha halpha
  obtain ⟨y, hy, hyc⟩ := ht c alpha hc halpha
  have hbx := hpreserve x hx b hb
  have hdy := hpreserve y hy d hd
  have hbne : rightAct b x ≠ alpha := by
    intro heq
    exact hab (rightAct_injective x (hxa.trans heq.symm))
  have hdne : rightAct d y ≠ alpha := by
    intro heq
    exact hcd (rightAct_injective y (hyc.trans heq.symm))
  obtain ⟨k, hk, hbk⟩ := hpoint _ _ hbx hdy hbne hdne
  have hkalpha : rightAct alpha k = alpha := (mem_rightStabilizer alpha k).mp hk.2
  refine ⟨x * k * y⁻¹, N.mul_mem (N.mul_mem hx hk.1) (N.inv_mem hy), ?_, ?_⟩
  · rw [← rightAct_mul, ← rightAct_mul, hxa, hkalpha, ← hyc,
      rightAct_mul, mul_inv_cancel, rightAct_one]
  · rw [← rightAct_mul, ← rightAct_mul, hbk, rightAct_mul, mul_inv_cancel, rightAct_one]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
