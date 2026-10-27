module

public import CFSG.ClassicalInvolution.Phan.Geometry.Basic

public section

namespace CFSG.ClassicalInvolution.Phan

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ}

variable (σ) in
@[expose] def NdVert (W : Submodule K (Fin d → K)) : Type _ :=
  {S : Submodule K (Fin d → K) // S ≤ W ∧ S ≠ ⊥ ∧ S ≠ W ∧ Nondeg σ S}

variable (σ) in
@[expose] def ndGraph (W : Submodule K (Fin d → K)) : SimpleGraph (NdVert σ W) where
  Adj S T := S.1 < T.1 ∨ T.1 < S.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (lt_irrefl _) (lt_irrefl _)⟩

end CFSG.ClassicalInvolution.Phan
