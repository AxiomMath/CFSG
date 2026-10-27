module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Monster.B.Co2 CFSG.RankThree.Native

@[expose] noncomputable def Qg : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure (permsA 2300 (qGens2 ()))

@[expose] noncomputable def dGenP (i : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 (dGens ())[i]!

@[expose] noncomputable def dEltP (k : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 (dElts ())[k]!

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

end
