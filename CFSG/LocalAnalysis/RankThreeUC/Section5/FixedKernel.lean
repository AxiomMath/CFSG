module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerSemiregular

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FixedKernel

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

variable {G : Type} [Group G] [Finite G]

theorem kernel_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B) (b : B) (hb : b ≠ 1) :
    LinearMap.ker (rep p (joint P T B) (bToJoint h.oddPrimeClassTwoAction b) - LinearMap.id) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  induction v using Additive.rec with | _ v => ?_
  induction v using QuotientGroup.induction_on with | _ x => ?_
  have hv' : rep p (joint P T B) (bToJoint h.oddPrimeClassTwoAction b)
      (Additive.ofMul (QuotientGroup.mk x : Quotient.Pbar P)) =
      Additive.ofMul (QuotientGroup.mk x) := by
    simpa [sub_eq_zero] using hv
  rw [rep_apply_mk] at hv'
  have h1 := Additive.ofMul.injective hv'
  rw [QuotientGroup.eq_iff_div_mem] at h1
  have hcomm : (b : G) * x * (b : G)⁻¹ * (x : G)⁻¹ ∈ centerP P := by
    rw [Quotient.mem_centerP]
    refine ⟨?_, ?_⟩
    · exact P.mul_mem (((Subgroup.mem_normalizer_iff.mp (h.oddPrimeClassTwoAction.setting.normB b.2)) x).mp x.2)
        (P.inv_mem x.2)
    · convert h1 using 1
      exact Subtype.ext (by simp [bToJoint_apply, CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.bAction_apply, div_eq_mul_inv])
  have := actor_isSemiregular_on_central_quotient h hpi b b.2 (fun h1 => hb (Subtype.ext h1)) x x.2 hcomm
  rw [Quotient.mem_centerP] at this
  obtain ⟨hx, hz⟩ := this
  show Additive.ofMul (QuotientGroup.mk x : Quotient.Pbar P) = 0
  have : (QuotientGroup.mk x : Quotient.Pbar P) = 1 := (QuotientGroup.eq_one_iff x).2 hz
  rw [this]; rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.FixedKernel
