module

public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import Certificates.Data.Kernel.Spor.MCount
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.SporSch.ChainKEnum
import CFSG.Certificates.Kernel.SporSch.ChainKOdd
import CFSG.Certificates.Kernel.SporSch.ChainKRepsL
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_cosetCount (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {g₀ : Equiv.Perm (Fin n)}
    {G₀ e : Nat} (hg₀ : imageList g₀ = (unpack n w G₀).toList)
    (_hG₀ : canonK n w (mask w) (n * w) G₀ = true) (he : 0 < e) (hk : 0 < k) {CS : List Nat}
    (hCS : CS.length = rcnt (LR 0))
    (hc : ∀ k₀ < rcnt (LR 0), cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
      CS.getD k₀ 0) :
    (cosetOrderTables (certificate hn gens words bv hbs) g₀ e).length = CS.sum :=
  chainK_cosetCount' hQ hn hbs hg₀ he hk hCS hc

theorem chainK_reps {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hsz : szOK n w = true)
    {mx cap : Nat} {CL : List ClassDatum} {reps : List (Equiv.Perm (Fin n))} {X : List Table}
    (hcls : allC (clsOneR n w tA tB mx cap) CL = true) (hdisj : clsDisj n w CL = true)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList)
    (hmx : 0 < mx) (hX : X.length = clsSize CL)
    (hne : allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2)) CL = true)
    (hcap : cap ≤ 2 ^ 32) :
    repsOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) X (reps.map toTable) cap = true ∧
      repSizes n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable) cap =
        CL.map (fun d => d.2.2.2.2.2.2.length) ∧
      (reps.map toTable).all (ordTest n mx) = true :=
  chainK_reps' hA hB hsz hcls hdisj hR hmx hX hne hcap

theorem chainK_repsTotal (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w (gens) words bv PS PSI LR TR TRI kS BP NS CH)
    {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hk : 0 < k)
    {mx my cap : Nat} {CL : List ClassDatum} {reps : List (Equiv.Perm (Fin n))}
    {ws : List (List Nat × Nat)} (hcls : allC (clsOneR n w tA tB mx cap) CL = true)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList)
    (_hmx : 0 < mx) (hmy : 0 < my) {CW : List (List Nat)}
    (hCW : CW.length = CL.length ∧ ∀ j < CL.length, (CW.getD j []).length = rcnt (LR 0) ∧
      ∀ k₀ < rcnt (LR 0), cntWordK n w (mask w) (n * w) (pidn n w) LR TR k mx my ws
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.1 k₀ = (CW.getD j []).getD k₀ 0)
    (hne : allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2)) CL = true) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn gens words bv hbs) my) cap (wordsTest n mx my ws) =
      ((List.range CL.length).map fun j =>
        (CL.getD j (0, 0, 0, [], [], [], [])).2.2.2.2.2.2.length * (CW.getD j []).sum).sum :=
  chainK_repsTotal' hn hbs hQ hA hB hk hcls hR hmy hCW hne

theorem chainK_odd (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {mo : Nat} {W : Nat → Nat}
    (h : oddK n w (mask w) (n * w) (pidn n w) LR TR k mo W 0 (ordK LR k) = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true :=
  chainK_odd' hQ hn hbs h

theorem abWordK_rep {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat}
    (hsz : szOK n w = true) (hA : imageList gA = (unpack n w A).toList)
    (hB : imageList gB = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    {wd : List Int} (hw : abOK wd = true) :
    imageList (evalCodes [gA, gB] wd) =
      (unpack n w (abWordK n w (mask w) (pidn n w) A Ai B Bi wd)).toList :=
  abWordK_rep' hsz hA hB hAi hBi hw

theorem commT_of_commK {g h : Equiv.Perm (Fin n)} {P Q : Nat}
    (hg : imageList g = (unpack n w P).toList) (hh : imageList h = (unpack n w Q).toList)
    (hc : commK n w (mask w) (n * w) P Q = true) :
    commT n (toTable g) (toTable h) = true :=
  commT_of_commK' hg hh hc

theorem ordTest_of_ordIs {g : Equiv.Perm (Fin n)} {P e : Nat} (hsz : szOK n w = true)
    (hg : imageList g = (unpack n w P).toList) (hP : canonK n w (mask w) (n * w) P = true)
    (he : 0 < e)
    (h : ordIs n w (mask w) (pidn n w) P (e - 1) = true) :
    ordTest n e (toTable g) = true :=
  ordTest_of_ordIs' hsz hg hP he h

theorem wordsTest_of_wordOrdK {gA gB : Equiv.Perm (Fin n)} {A B mx my : Nat}
    {ws : List (List Nat × Nat)} (hsz : szOK n w = true)
    (hA : imageList gA = (unpack n w A).toList) (hB : imageList gB = (unpack n w B).toList)
    (h : wordOrdK n w (mask w) (pidn n w) mx my ws A B = true) :
    wordsTest n mx my ws (toTable gA) (toTable gB) = true :=
  wordsTest_of_wordOrdK' hsz hA hB h

end CFSG.KS.SporSch.MOC

end
