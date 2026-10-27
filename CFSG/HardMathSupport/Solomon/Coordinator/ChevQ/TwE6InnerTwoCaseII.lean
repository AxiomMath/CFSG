module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoPeel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRankOne
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoSylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem twE6InnerNoA2Two_of_parts (hA : TwE6CaseIIA2Kill) (hB : TwE6CaseIICycNonA2)
    (hC : TwE6CaseIIRankTwo) : TwE6InnerNoA2Two := by
  intro K _ _ σ q hK hσ hq hq2 E₀ hE₀ hc hN hII
  have hK3 : ringChar K ≠ 3 := by
    refine ringChar_ne_three_of_not_dvd fun h3 => ?_
    rw [hK] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  obtain ⟨Fr, hFr, v, hv, g0, hg0C, hg0, hmono⟩ :=
    twE6SylowMonoTwo_holds K σ q hK hσ hq E₀ hE₀.isPGroup
  by_cases h0 : ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)
  · exact ⟨g0, hg0C, h0⟩
  by_cases hA2 : ∃ α β : Fin TwistTag.E6.tag.rank → ℤ, IsA2Pair α β ∧
      TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers (rootReflection α * rootReflection β))
  · obtain ⟨α, β, hαβ, hW⟩ := hA2
    refine twE6ToralBar_of_a2Peel K σ hK3 E₀ g0 hg0C hαβ (fun x hx => ?_)
      (hA K σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN hII Fr hFr v hv g0 hg0C hg0 hmono h0 α β hαβ hW)
    obtain ⟨t, ht, w, hw⟩ := hmono x hx
    exact ⟨t, ht, w, hW x hx t ht w hw, hw⟩
  have hA2' : ∀ α β : Fin TwistTag.E6.tag.rank → ℤ, IsA2Pair α β →
      ¬ TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers (rootReflection α * rootReflection β)) :=
    fun α β hαβ hW => hA2 ⟨α, β, hαβ, hW⟩
  by_cases hcyc : ∃ w : WeylGroup TwistTag.E6.tag, TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w)
  · obtain ⟨w, hw⟩ := hcyc
    exact hB K σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN hII Fr hFr v hv g0 hg0C hg0 hmono h0 w hw hA2'
  · exact hC K σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN hII Fr hFr v hv g0 hg0C hg0 hmono h0
      fun w hw => hcyc ⟨w, hw⟩

theorem twE6InnerNoA2Two_of_cycNonA2_rankTwo (hB : TwE6CaseIICycNonA2) (hC : TwE6CaseIIRankTwo) :
    TwE6InnerNoA2Two :=
  twE6InnerNoA2Two_of_parts twE6CaseIIA2Kill_holds hB hC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
