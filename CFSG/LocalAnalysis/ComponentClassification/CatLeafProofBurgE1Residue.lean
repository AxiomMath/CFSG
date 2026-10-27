module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def BurgE1D4OrderThreeInput
    : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Odd q → Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ∀ (t g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (δ : K ≃+* K), orderOf t = 2 → (δ = σ ∨ δ = σ⁻¹) →
      Odd (orderOf (MulAut.conj g * fieldActor (t := .D4) σ δ)) →
      MulAut.conj t * (MulAut.conj g * fieldActor (t := .D4) σ δ) =
        MulAut.conj g * fieldActor (t := .D4) σ δ * MulAut.conj t →
      ¬ ∀ x ∈ fixedSubgroup (MulAut.conj t), (MulAut.conj g * fieldActor (t := .D4) σ δ) x = x

@[expose] def BurgE1Residue
    : Prop :=
  BurgE1D4OrderThreeInput

end CFSG.ComponentClassification.CatLeafProof
