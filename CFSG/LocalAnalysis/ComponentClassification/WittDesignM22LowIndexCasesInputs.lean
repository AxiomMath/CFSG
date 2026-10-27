module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndex
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2195

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

@[expose] def orbY1 : Finset (Fin 22) := {0, 1, 5, 9, 15, 20, 21}

@[expose] def orbY2 : Finset (Fin 22) := {2, 3, 8, 14, 16, 17, 18}

@[expose] def orbY3 : Finset (Fin 22) := {6, 7, 10, 11, 12, 13, 19}

@[expose] def pairX2 : Finset (Fin 22) := {0, 1}

@[expose] def pairPartition : Finset (Finset (Fin 22)) := {{2, 9}, {17, 19}}

@[expose] def InP2 (f : Fin 22 → Fin 22) : Prop :=
  (∀ x ∈ hexad0, f x ∈ hexad0) ∧ (∀ x ∈ pairX2, f x ∈ pairX2) ∧
    pairPartition.image (fun s => s.image f) = pairPartition

instance : DecidablePred InP2 := fun f => by
  unfold InP2
  infer_instance

end CFSG.ComponentClassification.WittDesign
