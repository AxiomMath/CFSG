module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import Certificates.Certificate2195

public section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Sporadic.Mathieu

@[expose] def aTable : Array ℕ := #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17,
  18, 19, 20, 5]

@[expose] def aFun (x : Fin 22) : Fin 22 := ⟨aTable[x.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

end CFSG.ComponentClassification.WittDesign
