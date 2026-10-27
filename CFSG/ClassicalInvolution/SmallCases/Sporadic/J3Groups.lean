module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.ClassicalInvolution.J3Groups

open CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.J3Data

@[expose] noncomputable def pa : Equiv.Perm (Fin 20520) := permOfArr 20520 abArr[0]!

@[expose] noncomputable def pb : Equiv.Perm (Fin 20520) := permOfArr 20520 abArr[1]!

@[expose] noncomputable def P : Subgroup (Equiv.Perm (Fin 20520)) := Subgroup.closure {pa, pb}

@[expose] noncomputable def gen (T : Array (Array Nat)) (k : Nat) :
    Subgroup (Equiv.Perm (Fin 20520)) :=
  Subgroup.closure {g | ∃ i < k, permOfArr 20520 T[i]! = g}

@[expose] noncomputable def K : Subgroup (Equiv.Perm (Fin 20520)) := gen kStrong 2

@[expose] noncomputable def U : Subgroup (Equiv.Perm (Fin 20520)) := gen uStrong 4

@[expose] noncomputable def S : Subgroup (Equiv.Perm (Fin 20520)) := gen sStrong 4

end CFSG.ClassicalInvolution.J3Groups

end
