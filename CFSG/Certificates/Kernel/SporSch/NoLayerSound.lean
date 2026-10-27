module

public import Certificates.Data.Kernel.SporSch.NoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathCheckInputs
import CFSG.Certificates.Kernel.SporSch.ChainKNoLayer
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayerCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.QuasithinUnique.Id2519.MathNoLayer

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_noLayer (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {E : List (List Nat)}
    {EP : List Nat} (hb : bindLs n w E EP = true) (hid : memL (pidn n w) EP = true)
    (hE : nlE n w (mask w) (n * w) (pidn n w) LR TRI BP k PS PSI gens.length EP EP = true)
    {NB B : Nat} (hN : ordK LR k ≤ NB * B)
    (hK : ∀ s < NB, nlK n w (mask w) (n * w) (pidn n w) LR TR k EP (s * B) B = true) :
    noLayerOK n (toTabs E) (allTables (certificate hn gens words bv hbs)) = true :=
  chainK_noLayer' hQ hn hbs hb hid hE hN hK

end CFSG.KS.SporSch.MOC

end
