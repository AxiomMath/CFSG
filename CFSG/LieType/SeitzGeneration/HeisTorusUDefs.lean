module

public import CFSG.LieType.SeitzGeneration.HeisLinearDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def IsMonomialMat {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ j i i', A i j ≠ 0 → A i' j ≠ 0 → i = i'

@[expose] def IsCoordBlockOn {n : ℕ} (a b : Fin n) (g : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) → g i j = if i = j then 1 else 0

@[expose] noncomputable def unitaryHomology (h : UnitaryFieldData ℓ f K) {n : ℕ} (w : Fin n → K)
    (σ : K) : Matrix (Fin n) (Fin n) K :=
  1 + ((σ - 1) / ∑ i, h.bar (w i) * w i) • vecMulVec w (fun i => h.bar (w i))

@[expose] def TorusFourierGenU (h : UnitaryFieldData ℓ f K) (r : ℕ) : Prop :=
  ∀ ζ : K, IsPrimitiveRoot ζ r → ∀ H : Subgroup (GL (Fin r) K), H ≤ unitarySU ℓ f K r →
    (∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H) →
    (∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H) →
    H = unitarySU ℓ f K r

end CFSG.LieType.SeitzGeneration
