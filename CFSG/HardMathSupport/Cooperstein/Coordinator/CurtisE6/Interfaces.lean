module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Rank1
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTypeE6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

@[expose] def E6Surv27 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
      (ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)) (y : Fin m → k)
      (χ : ↥(e6Data_valid.minGroup K) → k) (J : Finset N6) (s : N6) (b : ℕ),
      IsSimpleRep ρ → IsCoverType (e6CoverRankOne K) ρ y χ J →
      (s = ⟨0, by decide⟩ ∨ s = ⟨5, by decide⟩) → b < n → J = Finset.univ.erase s →
      (∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
        if i = s then (algebraMap K k (u : K)) ^ (2 ^ b) else 1) →
      m = 27 ∧ ∀ A : Subgroup ↥(e6Data_valid.minGroup K), (∀ a ∈ A, a ^ 2 = 1) → A ≠ ⊥ →
        Nat.card A * Nat.card K ^ Module.finrank k (fixSub ρ A) < Nat.card K ^ 27

@[expose] def E6Surv78 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
      (ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)) (y : Fin m → k)
      (χ : ↥(e6Data_valid.minGroup K) → k) (J : Finset N6) (b : ℕ),
      IsSimpleRep ρ → IsCoverType (e6CoverRankOne K) ρ y χ J → b < n →
      J = Finset.univ.erase (⟨1, by decide⟩ : N6) →
      (∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
        if i = (⟨1, by decide⟩ : N6) then (algebraMap K k (u : K)) ^ (2 ^ b) else 1) →
      m = 78 ∧ ∀ A : Subgroup ↥(e6Data_valid.minGroup K), (∀ a ∈ A, a ^ 2 = 1) → A ≠ ⊥ →
        22 + Module.finrank k (fixSub ρ A) ≤ 78 ∧ Nat.card A ≤ Nat.card K ^ 16

@[expose] def E6InnerOfSqOne : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (α : MulAut ↥(adjointGroup .E6 K)),
    α * α = 1 →
    (∃ (g : ↥(adjointGroup .E6 K)) (a : Fin Tag.E6.rank → Kˣ), ∀ h : ↥(adjointGroup .E6 K),
      (α h : ModGL .E6 K) = (g : ModGL .E6 K) * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 a * (h : ModGL .E6 K) *
        (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹) →
    α ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
