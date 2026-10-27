module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

@[expose] def sumSqForm {ι K : Type*} [Fintype ι] [Semiring K] (v : ι → K) : K := v ⬝ᵥ v

@[expose] def negCoordGL {ι K : Type*} [Fintype ι] [DecidableEq ι] [Ring K] (s : Finset ι) :
    GL ι K :=
  TauCeti.diagGL fun i => if i ∈ s then -1 else 1

end CFSG.ClassicalGroups.Orthogonal
