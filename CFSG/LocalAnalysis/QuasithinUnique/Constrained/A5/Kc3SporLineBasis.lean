module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Irr

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique.Unc25G2.M2x

section Hall

variable {Γ : Type} [Group Γ] [Finite Γ] (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]

@[expose] def AllowedFibre (c : ℕ) : Prop :=
  c = 0 ∨ c = 60 ∨ c = 90 ∨ c = 120 ∨ c = 150 ∨ c = 210

instance (c : ℕ) : Decidable (AllowedFibre c) := by
  unfold AllowedFibre
  infer_instance

end Hall

end CFSG.QuasithinUnique.A5.Kc3SporLine
