module

public import CFSG.LieType.SeitzGeneration.HeisLinearDefs

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

@[expose] def ContainsDiagTorus (K : Subgroup (SpecialLinearGroup (Fin p) F)) : Prop :=
  ∀ g : SpecialLinearGroup (Fin p) F,
    (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = diagonal t) → g ∈ K

@[expose] def ContainsFourierTorus (ζ : F) (K : Subgroup (SpecialLinearGroup (Fin p) F)) : Prop :=
  ∀ g : SpecialLinearGroup (Fin p) F,
    (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) * heisFourierMat ζ =
      heisFourierMat ζ * diagonal t) → g ∈ K

@[expose] def RootSuppIn (I : Finset (Fin p)) (M : Matrix (Fin p) (Fin p) F) : Prop :=
  ∀ a b, M a b ≠ 0 → a ∈ I ∧ b ∉ I

@[expose] def zFix (ν : F) : Matrix (Fin p) (Fin p) F :=
  diagonal fun i => if (i : ℕ) = 0 then (ν ^ (p - 1))⁻¹ else ν

@[expose] noncomputable def fourierBirefl (ζ ν : F) : Matrix (Fin p) (Fin p) F :=
  heisFourierMat ζ * diagonal (fun i : Fin p =>
    if (i : ℕ) = 0 then ν else if (i : ℕ) = 1 then ν⁻¹ else 1) * (heisFourierMat ζ)⁻¹

end CFSG.LieType.SeitzGeneration
