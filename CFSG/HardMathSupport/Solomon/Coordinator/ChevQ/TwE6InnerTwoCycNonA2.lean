module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootVec
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadow
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadowDim
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Kinds
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree


theorem twE6CaseIICycNonA2_of_kinds (hk : E6Order3Kinds) : TwE6CaseIICycNonA2 := by
  intro K _ _ σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN hII Fr hFr v hv g0 hg0C hg0 hmono h0 w hW hA2'
  exfalso
  obtain ⟨x₁, hx₁'⟩ := not_forall.1 h0
  obtain ⟨hx₁, hx₁T⟩ := not_imp.1 hx₁'
  obtain ⟨t₁, ht₁, w₁, hw₁⟩ := hmono x₁ hx₁
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    rw [canonicalRep_one, mul_one] at hw₁
    exact hx₁T (hw₁ ▸ ht₁)
  have hw₁3 : w₁ ^ 3 = 1 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hw₁
  have hall : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 =
          t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
        u ∈ Subgroup.zpowers w₁ := fun x hx t ht u hxu =>
    mem_zpowers_of_pow_three_eq_one (hW x₁ hx₁ t₁ ht₁ w₁ hw₁) hw₁3 hw₁1 (hW x hx t ht u hxu)
      (pow_eq_one_of_twE6Frame_eq (hE₀.2 x hx) ht hxu)
  rcases hk w₁ hw₁3 hw₁1 with ⟨α, β, hαβ, hw⟩ | ⟨γ₁, γ₂, hγ, h₁, h₂, hfix, hμ, hNj⟩ | hk3
  ·
    refine hA2' α β hαβ fun x hx t ht u hxu => ?_
    have h := hall x hx t ht u hxu
    rwa [hw] at h
  ·
    set F := twE6RootVecFixer K σ g0 (a2Roots γ₁ γ₂) with hF
    have hover : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ →
        x ∈ F := fun x hx t ht hxt =>
      mem_twE6RootVecFixer_of_kind2A2 hK3 hE₀.2 hII hx ht hxt hγ h₁ h₂ hfix hμ hNj
    have hEF : ∀ x ∈ E₀, x ∈ F := by
      intro x hx
      obtain ⟨t, ht, u, hxu⟩ := hmono x hx
      rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hw₁3 (hall x hx t ht u hxu) with
        rfl | rfl | rfl
      · obtain ⟨s, hs, hxs⟩ := exists_twE6Frame_mul_eq ht ht₁ hxu hw₁
        rw [one_mul] at hxs
        have h := F.mul_mem (hover _ (mul_mem hx hx₁) s hs hxs)
          (F.inv_mem (hover x₁ hx₁ t₁ ht₁ hw₁))
        rwa [mul_inv_cancel_right] at h
      · exact hover x hx t ht hxu
      · obtain ⟨s, hs, hxs⟩ := exists_twE6Frame_inv_eq ht hxu
        rw [inv_inv] at hxs
        have h := F.inv_mem (hover _ (inv_mem hx) s hs hxs)
        rwa [inv_inv] at h
    refine hN (normalizesRGroup_of_monomial_fixed_rootVec q K σ hK hσ hK3 E₀ Fr hFr v g0 hg0C hg0
      hγ.isRoot_fst (hv γ₁) fun x hx => ?_)
    obtain ⟨t, ht, u, hxu⟩ := hmono x hx
    have hu := hall x hx t ht u hxu
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    have hxF := mem_twE6RootVecFixer.1 (hEF x hx)
    have hγ₁ : γ₁ ∈ a2Roots γ₁ γ₂ := Set.mem_insert _ _
    refine ⟨a, u, hxu, ?_, hxF γ₁ hγ₁, hxF (-γ₁) (neg_mem_a2Roots hγ₁)⟩
    exact MulAction.mem_stabilizer_iff.1
      (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h₁) hu)
  ·
    exact not_kind3A2_of_twE6FixDim_ne hK3 hE₀.2 hII hx₁ ht₁ hw₁ hk3

theorem twE6CaseIICycNonA2_holds : TwE6CaseIICycNonA2 :=
  twE6CaseIICycNonA2_of_kinds e6Order3Kinds_holds

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
