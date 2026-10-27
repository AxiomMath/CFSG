module

public import Certificates.Data.Kernel.SporSch.MathieuBT
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
import CFSG.Certificates.Kernel.SporSch.ChainKZTot
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

@[expose] def ClassEqK (n w : Nat) (LR TR TRI : Nat → Nat) (BP k : Nat) (XL CL : List Nat) :
    Prop :=
  XL.length = CL.length ∧
    (∀ i < XL.length, repK n w (mask w) (n * w) BP k LR TR TRI (XL.getD i 0) (CL.getD i 0) =
      true) ∧
    (∀ i < XL.length, ∀ j < i,
      distK n w (mask w) (n * w) BP k LR TR TRI (XL.getD j 0) (XL.getD i 0) = true) ∧
    Nat.succ (sumAllK (ordK LR k) CL XL.length) = ordK LR k

@[expose] def ZScans (n w mx my r : Nat) (ws : List (List Nat × Nat)) (XL : List Nat)
    (CS : List ClsD) (SC : List (List (List Nat))) : Prop :=
  SC.length = XL.length ∧ ∀ i < XL.length, ordC n w (mask w) (XL.getD i 0) = r →
    (SC.getD i []).length = CS.length ∧ ∀ j < CS.length,
      (CS.getD j clsD0).c ≤ ((SC.getD i []).getD j []).length * 256 ∧
      ∀ b < ((SC.getD i []).getD j []).length,
        cntZK n w (mask w) (pidn n w) mx my ws (XL.getD i 0) (CS.getD j clsD0) (b * 256) 256 =
          ((SC.getD i []).getD j []).getD b 0

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem classEq_sound (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {XL CL : List Nat}
    (hE : ClassEqK n w LR TR TRI BP k XL CL) {mo : Nat} (hmo : 1 < mo) (hk64 : k ≤ 64) :
    (orderTables (certificate hn gens words bv hbs) mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length ∧
      (cosetOrderTables (certificate hn gens words bv hbs) 1 mo).length =
        sumOrdK n w (mask w) (ordK LR k) XL CL mo XL.length :=
  classEq_sound' hQ hn hbs hk64 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hmo

theorem classOK_sound (hn : 1 ≤ n) {gA gB : Equiv.Perm (Fin n)} {bv : Vector (Fin n) k}
    (hbs : bv.toList.Nodup) (hQ : ChainK n w [gA, gB] words bv PS PSI LR TR TRI kS BP NS CH)
    {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) {mx cap : Nat}
    {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hmx : 0 < mx)
    (hX : (orderTables (certificate hn [gA, gB] words bv hbs) mx).length = (CS.map ClsD.c).sum) :
    classOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹)
      (orderTables (certificate hn [gA, gB] words bv hbs) mx) cap = true :=
  classOK_sound' hQ hn hbs hA hB hcls hRs hmx hX

theorem zReps_sound (hn : 1 ≤ n) {gA gB : Equiv.Perm (Fin n)} {bv : Vector (Fin n) k}
    (hbs : bv.toList.Nodup) (hQ : ChainK n w [gA, gB] words bv PS PSI LR TR TRI kS BP NS CH)
    {XL CL : List Nat} (hE : ClassEqK n w LR TR TRI BP k XL CL) (hk64 : k ≤ 64)
    {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) {mx my r cap : Nat}
    {CS : List ClsD} {reps : List (Equiv.Perm (Fin n))} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hR : reps.length = CS.length ∧ ∀ j < CS.length,
      imageList (reps.getD j 1) = (unpack n w (CS.getD j clsD0).R).toList)
    (hmx : 0 < mx) (hmy : 0 < my) (hr : 1 < r) {ws : List (List Nat × Nat)}
    (hws : ([0, 1], r) ∈ ws) {SC : List (List (List Nat))}
    (hSC : ZScans n w mx my r ws XL CS SC) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn [gA, gB] words bv hbs) my) cap (wordsTest n mx my ws) =
      zTotK n w (mask w) (ordK LR k) XL CL SC r XL.length :=
  zReps_sound' hQ hn hbs hk64 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hA hB hcls hRs hR hmx hmy hr hws hSC

theorem zClass_sound (hn : 1 ≤ n) {gA gB : Equiv.Perm (Fin n)} {bv : Vector (Fin n) k}
    (hbs : bv.toList.Nodup) (hQ : ChainK n w [gA, gB] words bv PS PSI LR TR TRI kS BP NS CH)
    {XL CL : List Nat} (hE : ClassEqK n w LR TR TRI BP k XL CL) (hk64 : k ≤ 64)
    {tA tB : List Nat} (hA : tA = imageList gA) (hB : tB = imageList gB) {mx my r s cap : Nat}
    {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hmx : 0 < mx) (hmy : 0 < my)
    (hr : 1 < r) (hs : 0 < s)
    (hX : (orderTables (certificate hn [gA, gB] words bv hbs) mx).length = (CS.map ClsD.c).sum)
    {SC : List (List (List Nat))}
    (hSC : ZScans n w mx my r [([0, 1], r), ([0, 1, 2, 3], s)] XL CS SC) :
    classTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹)
        (orderTables (certificate hn [gA, gB] words bv hbs) mx)
        (orderTables (certificate hn [gA, gB] words bv hbs) my) cap r s mx my =
      zTotK n w (mask w) (ordK LR k) XL CL SC r XL.length :=
  zClass_sound' hQ hn hbs hk64 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hA hB hcls hRs hmx hmy hr hs hX hSC

theorem chainK_oddB (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {mo L NB : Nat} {W : Nat → Nat}
    (hL : ordK LR k ≤ NB * L)
    (h : ∀ s < NB, oddK n w (mask w) (n * w) (pidn n w) LR TR k mo W (s * L) L = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true :=
  chainK_oddB' hQ hn hbs hL h

end CFSG.KS.SporSch.MBT

end
