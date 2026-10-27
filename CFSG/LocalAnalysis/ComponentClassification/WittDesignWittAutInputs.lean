module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittUnique
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2028
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2195
public import Certificates.Certificate2031
public import Certificates.Certificate2033
public import Certificates.Certificate2034

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Monster.B.Classical.Plane
open scoped Pointwise

@[expose] def phiFun (x : Fin 22) : Fin 21 := ⟨phiTab[x.val]! % 21, Nat.mod_lt _ (by norm_num)⟩

@[expose] def psiFun (y : Fin 21) : Fin 22 := ⟨psiTab[y.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

@[expose] def sigmaFun (x : Fin 22) : Fin 22 := ⟨sigmaTab[x.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

end CFSG.ComponentClassification.WittDesign
