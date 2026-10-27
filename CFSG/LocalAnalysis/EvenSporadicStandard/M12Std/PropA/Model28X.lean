module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.CheckWord
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv

@[expose] noncomputable def ggD (l : ℕ) : Perm (Fin 28) := if l = 0 then pA else pB

@[expose] noncomputable def x28 : Perm (Fin 28) := wordP ggD 2 Data.wx0

end CFSG.EvenSporadicStandard.M12Std.PropA
