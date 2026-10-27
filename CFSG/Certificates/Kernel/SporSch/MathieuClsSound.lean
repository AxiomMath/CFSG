module

public import Certificates.Data.Kernel.SporSch.MathieuCls
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
import CFSG.Certificates.Kernel.SporSch.ChainKReps
import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

@[expose] def clsD0 : ClsD := ⟨0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
  fun _ => 0, fun _ => 0⟩

@[expose] def ClsOK (n w : Nat) (tA tB : List Nat) (mx cap : Nat) (CL : List ClsD) : Prop :=
  ∀ j < CL.length, clsHdK n w (mask w) mx cap (CL.getD j clsD0) = true ∧
    (∀ k < (CL.getD j clsD0).c, clsElemK n w (mask w) (n * w) (packL w tA)
      (pinvS n w (mask w) (packL w tA)) (packL w tB) (pinvS n w (mask w) (packL w tB))
      (CL.getD j clsD0) k = true) ∧
    ∀ i < j, notInK (CL.getD i clsD0) (CL.getD j clsD0).R = true

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_reps3 {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hsz : szOK n w = true)
    {mx cap : Nat} {CL : List ClsD} {reps : List (Equiv.Perm (Fin n))} {X : List Table}
    (hcls : ClsOK n w tA tB mx cap CL)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j clsD0).R).toList)
    (hmx : 0 < mx) (hX : X.length = (CL.map ClsD.c).sum) :
    repsOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) X (reps.map toTable) cap = true ∧
      repSizes n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable) cap =
        CL.map ClsD.c ∧
      (reps.map toTable).all (ordTest n mx) = true := by
  subst hA hB
  have hf := CFSG.KS.Raw.Orb.szOK_facts hsz
  have hn := szOK_lt hsz
  have hwn : n < 2 ^ w := by omega
  have pA := (prep_packL (g := gA) hf.2).1
  have pB := (prep_packL (g := gB) hf.2).1
  exact reps_of_data hn (CFSG.KS.PF.w_pos hf.2) pA (prep_pinvS hwn pA).1 pB (prep_pinvS hwn pB).1
    hcls ⟨hR.1, fun j hj => prep_of_imageList (hR.2 j hj)⟩ hmx hX

theorem chainK_repsTotal3 (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
    {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat}
    (hA : tA = imageList gA) (hB : tB = imageList gB) (hk : 2 ≤ k)
    {mx my cap : Nat} {CL : List ClsD} {reps : List (Equiv.Perm (Fin n))}
    {ws : List (List Nat × Nat)} (hcls : ClsOK n w tA tB mx cap CL)
    (hR : reps.length = CL.length ∧ ∀ j < CL.length,
      imageList (reps.getD j 1) = (unpack n w (CL.getD j clsD0).R).toList)
    (hmx : 0 < mx) (hmy : 0 < my) {CW : List (List (List Nat))}
    (hCW : CW.length = CL.length ∧ ∀ j < CL.length, Counts2 LR (CW.getD j [])
      (cntWord2K n w (mask w) (n * w) (pidn n w) LR TR k mx my ws (CL.getD j clsD0).R)) :
    repsTotal n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable)
        (orderTables (certificate hn gens words bv hbs) my) cap (wordsTest n mx my ws) =
      ((List.range CL.length).map fun j =>
        (CL.getD j clsD0).c * ((CW.getD j []).map List.sum).sum).sum := by
  have hsz := chainK_szOK hQ
  have hsizes := (chainK_reps3 hA hB hsz hcls hR hmx (X := List.replicate (CL.map ClsD.c).sum #[])
    (by simp)).2.1
  have hlen : reps.length = CL.length := hR.1
  refine repsTotal_eq hlen (fun j hj => ?_) (fun j hj => ?_)
  · have e := congrArg (fun l => l[j]?) hsizes
    simp only [repSizes, List.map_map, List.getElem?_map, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (hlen ▸ hj : j < CL.length), Option.map_some,
      Option.some.injEq, Function.comp_apply] at e
    rw [e, List.getD_eq_getElem _ _ (hlen ▸ hj)]
  · have hj' : j < CL.length := hlen ▸ hj
    have pR := prep_of_imageList (hR.2 j hj')
    rw [List.getD_eq_getElem _ _ hj] at pR
    exact countWord2' hQ hn hbs pR hmy ws hk (hCW.2 j hj')

end CFSG.KS.SporSch.MOC

end
