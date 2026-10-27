module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J4.QTData

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu

@[expose] def permOfCycles (cs : List (List (Fin 24))) : Equiv.Perm (Fin 24) :=
  (cs.map List.formPerm).prod

@[expose] def tauOf : ℕ → Equiv.Perm (Fin 24)
  | 0 => permOfCycles cyc0
  | 1 => permOfCycles cyc1
  | _ => permOfCycles cyc2

@[expose] def starPermOf : ℕ → List ℕ
  | 0 => starPerm0
  | 1 => starPerm1
  | _ => starPerm2

@[expose] def wordOf : ℕ → List ℕ
  | 0 => word0
  | 1 => word1
  | _ => word2

@[expose] def genM24 : ℕ → Equiv.Perm (Fin 24)
  | 0 => m24gA
  | 1 => m24gB
  | _ => m24gB⁻¹

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
