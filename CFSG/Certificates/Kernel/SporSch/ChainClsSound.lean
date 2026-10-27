module

public import Certificates.Data.Kernel.SporSch.ChainCls
import CFSG.Certificates.Kernel.SporSch.ChainKClasses
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.KS.SporSch.ChainCls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_commAllCount (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {gs : List (Equiv.Perm (Fin n))}
    {G : Nat → Nat}
    (hG : ∀ i < gs.length, imageList (gs.getD i 1) = (unpack n w (G i)).toList ∧
      canonK n w (mask w) (n * w) (G i) = true)
    {L : Nat} {CS : List Nat} (hL : ordK LR k ≤ CS.length * L)
    (hc : ∀ s < CS.length, commCntK n w (mask w) (n * w) (pidn n w) LR TR k G gs.length
      (ordK LR k) (s * L) L = CS.getD s 0) :
    (allTables (certificate hn gens words bv hbs)).countP (commAll n (gs.map toTable)) =
      CS.sum :=
  chainK_commAllCount' hQ hn hbs hG hL hc

theorem chainK_classes (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
    {LB CJ RP SZ ZC : Nat → Nat} {c cap L NB : Nat} (hL : ordK LR k ≤ NB * L)
    (hinv : ∀ s < NB, allBlk (s * L) (fun j => bIf(Nat.blt j (ordK LR k),
      clsInvK n w (mask w) (n * w) (pidn n w) LR TR k PS PSI gens.length LB CJ RP c
        (ordK LR k) j, true)) L = true)
    (hrep : ∀ l < c, clsRepK n w (mask w) (n * w) (pidn n w) LR TR k LB RP SZ ZC
      (ordK LR k) l = true)
    (hcap : ∀ l < c, SZ l ≤ cap) :
    classOK n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap = true ∧
      (classes n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap).map (fun c => c.2.1.size) =
        (List.range c).map SZ ∧
      (classes n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap).map
          (fun c => (allTables (certificate hn gens words bv hbs)).countP (commT n c.1)) =
        (List.range c).map ZC :=
  chainK_classes' hn hbs hQ hL hinv hrep hcap

end CFSG.KS.SporSch.ChainCls

end
