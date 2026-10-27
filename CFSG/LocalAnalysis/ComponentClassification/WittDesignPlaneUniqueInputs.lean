module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneFrame
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public import CFSG.Monster.B.Classical.PlaneIncidence
public meta import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
public meta import Mathlib
public import Mathlib

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open Equiv CFSG.Monster.B.Classical.Plane

@[expose] def enc (j : Fin 5) (x : Fin 4) : Fin 21 := ⟨1 + 4 * j + x, by omega⟩

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}

section Squares

variable (h : IsSteinerPlane 𝓛) (p₀ : P)

end Squares

end CFSG.ComponentClassification.WittDesign
