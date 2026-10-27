module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem ringEquiv_mul_comm_of_finite (K : Type) [Field K] [Finite K] (σ τ : K ≃+* K) :
    σ * τ = τ * σ := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  let toAlg : (K ≃+* K) → (K ≃ₐ[ZMod (ringChar K)] K) := fun σ =>
    AlgEquiv.ofRingEquiv (f := σ) fun x => by
      have h := RingHom.congr_fun
        (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod (ringChar K)) K))
          (algebraMap (ZMod (ringChar K)) K)) x
      exact h
  have hmul : ∀ a b : K ≃+* K, toAlg (a * b) = toAlg a * toAlg b :=
    fun a b => AlgEquiv.ext fun x => rfl
  letI : CommGroup (K ≃ₐ[ZMod (ringChar K)] K) := IsCyclic.commGroup
  have hc := mul_comm (toAlg σ) (toAlg τ)
  rw [← hmul σ τ, ← hmul τ σ] at hc
  exact RingEquiv.ext fun x => congrArg (fun f : K ≃ₐ[ZMod (ringChar K)] K => f x) hc

section E8Normal

theorem exists_E8_normal_form (K : Type) [Field K] [Finite K]
    (α : MulAut (adjointGroup .E8 K)) :
    ∃ x : ModGL .E8 K, x ∈ adjointGroup .E8 K ∧ ∃ σ : K ≃+* K, ∀ h : adjointGroup .E8 K,
      (α h : ModGL .E8 K) = x * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E8 K) * x⁻¹ := by
  obtain ⟨g, a, σ, ε, hα⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K).2.2 α
  have hQ : ∀ n : ℕ, exactQ .E8 K n = 1 := fun n => rfl
  refine ⟨(g : ModGL .E8 K) * rootDiagUnit .E8 a,
    Subgroup.mul_mem _ g.2 (CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_adjointGroup_E8 (K := K) a),
    σ, fun h => ?_⟩
  rw [hα h, hQ]
  group

end E8Normal

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal

end
