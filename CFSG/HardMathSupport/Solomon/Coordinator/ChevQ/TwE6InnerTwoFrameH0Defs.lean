module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

@[expose] def TwE6SylowMonoTwoAt : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 →
    ∀ E : Subgroup (twistedE6RootGroup K σ), IsPGroup 3 E →
    ∀ h₀ ∈ E, (∀ x ∈ E, x * h₀ = h₀ * x) → h₀ ^ 3 = 1 → twE6FixDim K σ h₀ = 24 →
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) ∧
    ∃ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) ∧
    ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
      (∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (h₀ : ModGL TwistTag.E6.tag K) * g0 = rootDiagUnit TwistTag.E6.tag a ∧
        ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
          (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3)) ∧
      ∀ x ∈ E, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * g0 =
            t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
