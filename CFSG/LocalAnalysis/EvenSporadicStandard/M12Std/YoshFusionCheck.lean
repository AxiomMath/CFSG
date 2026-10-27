module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFusionData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshEnumTools
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Data

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def jgenW (α : ℕ) (j : Fin 9) : List (Fin 9 × Bool) := swN ((jgenL α).getD j.val [])

@[expose] def sgenW (α : ℕ) (j : Fin 9) : List (Fin 9 × Bool) := swN ((sgenL α).getD j.val [])

@[expose] def sigmaRelQ (α : ℕ) : List (List (Fin 8 × Bool)) :=
  (List.finRange 9).map fun j =>
    [((4 : Fin 8), false)] ++ substW (toQ α α) (jgenW α j) ++ [((4 : Fin 8), true)] ++
      invW (substW (toQ α α) (substW (jgenW α) (sgenW α j)))

@[expose] def sigmaQCheck (α : ℕ) : Bool :=
  wordsTrivial 24 (fun i : Fin 8 => (qGens α α)[i.val]!) (fun i : Fin 8 => (qInvs α α)[i.val]!)
    (sigmaRelQ α)

@[expose] def nT (α k : ℕ) (w : List (Fin 9 × Bool)) : Table := modelT 16 9 (nGens α k) w

@[expose] def nEnum (α k : ℕ) : Array Table := (mulClosureS 16 16 (nGens α k) 4000).1

@[expose] def conjugatesTo (α k : ℕ) (t₁ t₂ : Table) : Bool :=
  (nEnum α k).any fun m => tblEq 16 (conjT 16 m t₁) t₂

@[expose] def jIn (α : ℕ) (W : List (Fin 9 × Bool)) : List (Fin 9 × Bool) := substW (jgenW α) W

@[expose] def jOut (α : ℕ) (W : List (Fin 9 × Bool)) : List (Fin 9 × Bool) :=
  substW (jgenW α) (substW (sgenW α) W)

@[expose] def chainRun (α k : ℕ) :
    List (Fin 9 × Bool) → List (List Int × Bool) → Option (List (Fin 9 × Bool))
  | w, [] => some w
  | w, (W, dir) :: rest =>
    if conjugatesTo α k (nT α k w)
        (nT α k (if dir then jOut α (swN W) else jIn α (swN W))) then
      chainRun α k (if dir then jIn α (swN W) else jOut α (swN W)) rest
    else none

@[expose] def isSqN (α k : ℕ) (t : Table) : Bool :=
  (nEnum α k).any fun z => tblEq 16 (compT 16 z z) t

@[expose] def isCommN (α k : ℕ) (t : Table) : Bool :=
  let C := (nEnum α k).filter (commTT 16 t)
  C.any fun a => C.any fun b => tblEq 16 (commutatorT 16 a b) t

@[expose] def witnessOK (α k : ℕ) (t : Table) : Bool := isSqN α k t || isCommN α k t

@[expose] def goodReps (α k : ℕ) : List (List (Fin 9 × Bool)) :=
  (goodChains α k).filterMap fun c => chainRun α k (swN c.1) c.2

@[expose] def badReps (α k : ℕ) : List (List (Fin 9 × Bool)) :=
  (badChains α k).filterMap fun c => chainRun α k (swN c.1) c.2

@[expose] def fusionChainsCheck (α k : ℕ) : Bool :=
  (goodChains α k).all (fun c => c.1 == [6] && (chainRun α k (swN c.1) c.2).isSome) &&
  (badChains α k).all (fun c =>
    witnessOK α k (nT α k (swN c.1)) && (chainRun α k (swN c.1) c.2).isSome)

@[expose] def classTabs (α k : ℕ) (t : Table) : List Table :=
  (nEnum α k).toList.map fun m => conjT 16 m t

@[expose] def goodCount (α : ℕ) : ℕ := if α = 0 then 80 else 200

@[expose] def goodTabs (α k : ℕ) : List Table :=
  (goodReps α k).flatMap fun w => classTabs α k (nT α k w)

@[expose] def badTabs (α k : ℕ) : List Table :=
  (badReps α k).flatMap fun w => classTabs α k (nT α k w)

@[expose] def fusionCoverCheck (α k : ℕ) : Bool :=
  let L := (nEnum α k).toList
  let good := goodTabs α k
  let bad := badTabs α k
  L.all (fun y => !involOK 16 y || memTab 16 good y || memTab 16 bad y) &&
    (L.filter (memTab 16 good)).length == goodCount α

@[expose] def fusionCheck : Bool :=
  [0, 1].all fun α => sigmaQCheck α && [0, 1].all fun k =>
    fusionChainsCheck α k && fusionCoverCheck α k

end CFSG.EvenSporadicStandard.M12Std.Yosh
