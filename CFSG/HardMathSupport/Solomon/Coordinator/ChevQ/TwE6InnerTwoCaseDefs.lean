module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def TwE6WeylPartsIn (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (S : Subgroup (WeylGroup TwistTag.E6.tag)) : Prop :=
  ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
    ∀ w : WeylGroup TwistTag.E6.tag,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 =
        t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w → w ∈ S

@[expose] def TwE6CaseIIA2Kill : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 → ringChar K ≠ 3 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → (∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * g0 =
            t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) →
      ¬ (∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∈
            torusGroup TwistTag.E6.tag (AlgebraicClosure K)) →
    ∀ α β : Fin TwistTag.E6.tag.rank → ℤ, IsA2Pair α β →
      TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers (rootReflection α * rootReflection β)) →
      ∀ x ∈ E₀,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 ∈
            torusGroup TwistTag.E6.tag (AlgebraicClosure K) →
          ∃ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
            g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
                g0 = rootDiagUnit TwistTag.E6.tag b ∧ rootChar b α = 1 ∧ rootChar b β = 1

@[expose] def TwE6CaseIICycNonA2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 → ringChar K ≠ 3 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → (∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * g0 =
            t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) →
      ¬ (∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∈
            torusGroup TwistTag.E6.tag (AlgebraicClosure K)) →
    ∀ w : WeylGroup TwistTag.E6.tag, TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w) →
      (∀ α β : Fin TwistTag.E6.tag.rank → ℤ, IsA2Pair α β →
        ¬ TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers (rootReflection α * rootReflection β))) →
      TwE6ToralBar K σ E₀

@[expose] def TwE6CaseIIRankTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 → ringChar K ≠ 3 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → (∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * g0 =
            t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) →
      ¬ (∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∈
            torusGroup TwistTag.E6.tag (AlgebraicClosure K)) →
      (∀ w : WeylGroup TwistTag.E6.tag, ¬ TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w)) →
      TwE6ToralBar K σ E₀

@[expose] def TwE6CaseIFrameH0 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 → ringChar K ≠ 3 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
    ∀ h₀ ∈ E₀, h₀ ≠ 1 → twE6FixDim K σ h₀ = 24 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
          g0 = rootDiagUnit TwistTag.E6.tag a →
      (∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
        (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3)) →
      (∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * g0 =
            t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) →
      TwE6All24PlaneIn K σ E₀ ∨ TwE6ToralBar K σ E₀

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
