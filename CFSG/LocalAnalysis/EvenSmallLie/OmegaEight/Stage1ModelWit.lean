module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Q3Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def oSetCheckW (ε : Eps) (T : Array (Array ℕ)) : Bool :=
  let n := deg ε
  let M := T.map (maskOf ε)
  allLt n (fun z => inOT ε z == inO ε z) &&
    (pBaseA ε).all (inOT ε) &&
    allLt n (fun z => !(inOT ε z) || (List.range 64).any fun y => (psiT ε y)[0]! == z) &&
    T.size == nOrb ε &&
    allLt T.size (fun i => isInvA n T[i]! (invCand n T[i]!) && memL ε T[i]!) &&
    allLt T.size (fun i => allLt i fun j => (List.range n).any fun z => (M[i]!)[z]! != (M[j]!)[z]!)

@[expose] def r3CheckW (T : Array (Array ℕ)) : Bool :=
  eqA 120 T[0]! (idA 120) &&
    allLt T.size (fun i => !((uOrig .plus).all fun s => stabB s (maskOf .plus T[i]!)) || i == 0)

structure UCls where
  cls : Array (Option (ℕ × ℕ))
  reps : Array ℕ

@[expose] def clsOfW (D : UCls) (i : ℕ) : Option (ℕ × ℕ) := D.cls.getD i none

@[expose] def nClsW (D : UCls) : ℕ := D.reps.size

@[expose] def repOfW (D : UCls) (c : ℕ) : ℕ := D.reps.getD c 0

@[expose] def membersOfW (D : UCls) (c : ℕ) : List ℕ :=
  (List.range 4096).filter fun i => ((clsOfW D i).map Prod.fst) == some c

@[expose] def membersTabW (D : UCls) : Array (List ℕ) :=
  Array.ofFn (n := nClsW D) fun c => membersOfW D c.val

@[expose] def adjBW (ε : Eps) (S : Array (Array ℕ)) (T : Array (List ℕ)) (c c' : ℕ) : Bool :=
  let n := deg ε
  (T.getD c []).all fun i => (T.getD c' []).all fun i' =>
    eqA n (compA n (S.getD i #[]) (S.getD i' #[])) (compA n (S.getD i' #[]) (S.getD i #[]))

@[expose] def adjTabW (ε : Eps) (S : Array (Array ℕ)) (D : UCls) : Array (Array Bool) :=
  let T := membersTabW D
  Array.ofFn (n := nClsW D) fun c => Array.ofFn (n := nClsW D) fun c' => adjBW ε S T c c'

@[expose] def adjTW (ε : Eps) (S : Array (Array ℕ)) (D : UCls) (c c' : ℕ) : Bool :=
  ((adjTabW ε S D).getD c #[]).getD c' false

@[expose] def okPreW (ε : Eps) (S : Array (Array ℕ)) (D : UCls) (d : List Bool) : Bool :=
  let da := d.toArray
  match d.getLast? with
  | some true => adjTW ε S D (d.length - 1) (d.length - 1) &&
      allLt (d.length - 1) fun c' => !(da.getD c' false) || adjTW ε S D c' (d.length - 1)
  | _ => true

@[expose] def sumSelW (D : UCls) (d : List Bool) : ℕ :=
  let da := d.toArray
  ((List.range 4096).filter fun i => selB da (clsOfW D i)).length

@[expose] def finalOKW (ε : Eps) (S : Array (Array ℕ)) (D : UCls) (w : List ℤ) (d : List Bool) :
    Bool :=
  let n := deg ε
  let da := d.toArray
  let l := lWord ε w
  let a := psiT ε 1
  memL ε l && isInvA n l (invCand n l) && !eqA n (conjA n l a) a &&
    allLt 4096 fun i => !(selB da (clsOfW D i)) ||
      (let y := conjA n l (S.getD i #[])
       (List.range 4096).any fun k => eqA n y (S.getD k #[]) && selB da (clsOfW D k))

@[expose] def s5CheckW (ε : Eps) (S : Array (Array ℕ)) (D : UCls) : Bool :=
  let n := deg ε
  S.size == 4096 &&
    allLt 4096 (fun i => isInvA n (S.getD i #[]) (invCand n (S.getD i #[])) &&
      (S.getD i #[]).size == n && memU ε (S.getD i #[])) &&
    allLt 4096 (fun i => allLt i fun j => !eqA n (S.getD i #[]) (S.getD j #[])) &&
    allLt 4096 (fun i => match clsOfW D i with
      | none => !(isInvol n (S.getD i #[]))
      | some (c, j) => decide (c < nClsW D) && decide (j < 4096) && isInvol n (S.getD i #[]) &&
          eqA n (S.getD i #[]) (conjA n (S.getD j #[]) (S.getD (repOfW D c) #[]))) &&
    allLt (nClsW D) (fun c => decide (repOfW D c < 4096)) &&
    (enumAux (okPreW ε S D) (nClsW D) []).all fun d =>
      sumSelW D d != 63 || (cands ε).any fun w => finalOKW ε S D w d

@[expose] def fMasksAW (F : Array (Array ℕ)) : Array (Array Bool) := F.map (fmask flagA)

@[expose] def fMasksBW (F : Array (Array ℕ)) : Array (Array Bool) := F.map (fmask flagB)

@[expose] def q3CheckW (F : Array (Array ℕ)) : Bool :=
  let us := uOrig .plus
  allLt 6 (fun k => (uArr .plus k)[0]! == 0) &&
  F.size == 315 && eqA 120 F[0]! (idA 120) &&
  allLt F.size (fun j => isInvA 120 F[j]! (invCand 120 F[j]!) && memP .plus F[j]!) &&
  allLt F.size (fun j => allLt j fun j' => (List.range 120).any fun z =>
    ((fMasksAW F)[j]!).getD z false != ((fMasksAW F)[j']!).getD z false ||
      ((fMasksBW F)[j]!).getD z false != ((fMasksBW F)[j']!).getD z false) &&
  us.all (fun s => stabB s flagA && stabB s flagB) &&
  allLt F.size (fun j => !(us.all fun s => stabB s (fMasksAW F)[j]! && stabB s (fMasksBW F)[j]!) ||
    j == 0) &&
  isInvA 360 rho2Arr (invCand 360 rho2Arr) &&
  allLt 6 (fun k => eqA 120 (OmegaEight.copy0Arr (utArr k)) (uArr .plus k) &&
    memU .plus (sigArr (utArr k))) &&
  allLt 6 (fun j => eqA 120 (sigArr (psiTT .plus (2 ^ j))) (sigTarget j))

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
