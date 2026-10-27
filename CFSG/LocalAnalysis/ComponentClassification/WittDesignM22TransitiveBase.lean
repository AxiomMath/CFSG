
module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import Certificates.Data.CFSGNative.Mathieu.M22

@[expose] public section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Sporadic.Mathieu

@[expose] def baseTriple : Fin 3 ↪ Fin 22 := ⟨![0, 1, 2], by decide⟩

theorem mem_stabilizer_baseTriple_iff {g : M22} :
    g ∈ stabilizer M22 baseTriple ↔
      (g : Equiv.Perm (Fin 22)) 0 = 0 ∧ (g : Equiv.Perm (Fin 22)) 1 = 1 ∧
        (g : Equiv.Perm (Fin 22)) 2 = 2 := by
  rw [MulAction.mem_stabilizer_iff, Function.Embedding.ext_iff, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_one]
  rfl

end CFSG.ComponentClassification.WittDesign
