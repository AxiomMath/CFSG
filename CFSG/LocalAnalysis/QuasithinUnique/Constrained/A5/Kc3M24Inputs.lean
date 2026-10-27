module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.QuasithinUnique.A5.Kc3M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M24Data

@[expose] def enc : ↥NativeSporadic.M24 → RN 24 := fun x => RN.enc (x : Equiv.Perm (Fin 24))

@[expose] def gR : List (RN 24) := [m24a, m24b, m24a⁻¹, m24b⁻¹].map enc

@[expose] def X : RN 24 := evalW gR xW

@[expose] def Ps : Std.HashSet (RN 24) := bfsSet (pW.map (evalW gR)) pDepth

@[expose] def Iset : Std.HashSet (RN 24) :=
  conjBfs (enc m24a) (enc m24b) (enc m24a⁻¹) (enc m24b⁻¹) (invSeeds Ps) 30

end CFSG.QuasithinUnique.A5.Kc3M24
