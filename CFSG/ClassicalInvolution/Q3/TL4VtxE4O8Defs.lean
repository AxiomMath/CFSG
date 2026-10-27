module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Data.E4QuatO8Check
public import Certificates.Data.E4QuatCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2

@[expose] noncomputable def perms (L : List (Array ℕ)) : List (Equiv.Perm (Fin 360)) :=
  L.map (permOfArr 360)

@[expose] noncomputable def u0 : Equiv.Perm (Fin 360) := permOfArr 360 (u0A ())

@[expose] noncomputable def v0 : Equiv.Perm (Fin 360) := permOfArr 360 (v0A ())

@[expose] noncomputable def three : Equiv.Perm (Fin 360) := permOfArr 360 (threeA ())

@[expose] noncomputable def K0 : Subgroup (Equiv.Perm (Fin 360)) := Subgroup.closure {u0, v0}

@[expose] noncomputable def L0P : List (Equiv.Perm (Fin 360)) := E4C.q8Elems (mainPerm 0) u0 v0

@[expose] noncomputable def wsP : List (Equiv.Perm (Fin 360)) := perms (wsA ())

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
