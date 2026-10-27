module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Data
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs

public section

namespace CFSG.QuasithinUnique.A5.Kc3M22
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.Unc25G2.M2x CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M22Data

@[expose] def enc : ↥NativeSporadic.M22 → RN 22 := fun x => RN.enc (x : Equiv.Perm (Fin 22))

@[expose] def gR : List (RN 22) := [m22a, m22b, m22a⁻¹, m22b⁻¹].map enc

end CFSG.QuasithinUnique.A5.Kc3M22
