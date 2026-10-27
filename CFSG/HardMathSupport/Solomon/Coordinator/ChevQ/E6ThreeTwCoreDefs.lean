module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineDefs
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree

section Fix

@[expose] def twE6FixDim (K : Type) [Field K] (σ : K ≃+* K) (s : twistedE6RootGroup K σ) : ℕ :=
  Module.finrank K (LinearMap.ker (((s : ModGL TwistTag.E6.tag K) :
    Module.End K (RootModule TwistTag.E6.tag K)) - 1))

@[expose] def TwE6InnerAll24 (K : Type) [Field K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) : Prop :=
  ∀ s : twistedE6RootGroup K σ, MulAut.conj s ∈ E → s ≠ 1 → twE6FixDim K σ s = 24

end Fix

@[expose] def TwE6ThreeA2LineStmt :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∃ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n

section Cubes

@[expose] def TwE6ThreeLayerGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E →
      TwE6InnerAll24 K σ E →
      (∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧ MulAut.conj s ∈ E) →
      ∀ i : Fin 3, L i ≤ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype

@[expose] def TwE6ThreeTorusGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E →
      TwE6InnerAll24 K σ E →
      (∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧ MulAut.conj s ∈ E) →
      T ≤ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ ⨆ i, L i

@[expose] def TwE6ThreeCompGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E →
      TwE6InnerAll24 K σ E →
      (∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧ MulAut.conj s ∈ E) →
      n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i)

@[expose] def TwE6NotAll24Gen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E →
      ¬ TwE6InnerAll24 K σ E → seitzHyperGamma 3 E = ⊤

end Cubes

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
