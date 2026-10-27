module

public import Certificates.Data.Kernel.O8.ModelW
public import CFSG.Certificates.Kernel.O8CPMSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelWit

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)

@[expose] def basicCheckG (n : ℕ) (T : ℕ → Array ℕ) (LS : Array (Array ℕ)) (LB : Array ℕ)
    (PS : Array (Array ℕ)) (PB : Array ℕ) (US : Array (Array ℕ)) (UB : Array ℕ)
    (pA uA G UR : ℕ → Array ℕ) : Bool :=
  allLt 64 (fun y => isInvA n (T y) (invCand n (T y)) && memG n LS LB (T y) &&
    memG n PS PB (T y) && memG n US UB (T y)) &&
  allLt 64 (fun y => allLt 64 fun y' =>
    eqA n (T (y ^^^ y')) (compA n (T y) (T y')) && (y == y' || !eqA n (T y) (T y'))) &&
  allLt 6 (fun i => isInvA n (pA i) (invCand n (pA i)) && memG n LS LB (pA i) &&
    allLt 64 fun y => eqA n (conjA n (pA i) (T y)) (T (bmulVec 6 6 (G i) y))) &&
  allLt 6 (fun k => isInvA n (uA k) (invCand n (uA k)) && memG n LS LB (uA k) &&
    allLt 64 fun y => eqA n (conjA n (uA k) (T y)) (T (bmulVec 6 6 (UR k) y))) &&
  allLt 64 (fun y => !(allLt 6 fun k => bmulVec 6 6 (UR k) y == y) || y == 0 || y == 1)

@[expose] def inOG (PT : ℕ → Array ℕ) (z : ℕ) : Bool := allLt 63 fun y => (PT (y + 1))[z]! != z

@[expose] def inOTG (n : ℕ) (PT : ℕ → Array ℕ) (z : ℕ) : Bool :=
  (Array.ofFn (n := n) fun z => inOG PT z.val).getD z false

@[expose] def maskOfG (n : ℕ) (PT : ℕ → Array ℕ) (g : Array ℕ) : Array Bool :=
  Array.ofFn (n := n) fun z => inOTG n PT (invCand n g)[z.val]!

@[expose] def oSetCheckG (n : ℕ) (PT : ℕ → Array ℕ) (LS : Array (Array ℕ)) (LB PB : Array ℕ)
    (nO : ℕ) (T : Array (Array ℕ)) : Bool :=
  let M := T.map (maskOfG n PT)
  allLt n (fun z => inOTG n PT z == inOG PT z) &&
    PB.all (inOTG n PT) &&
    allLt n (fun z => !(inOTG n PT z) || (List.range 64).any fun y => (PT y)[0]! == z) &&
    T.size == nO &&
    allLt T.size (fun i => isInvA n T[i]! (invCand n T[i]!) && memG n LS LB T[i]!) &&
    allLt T.size (fun i => allLt i fun j => (List.range n).any fun z => (M[i]!)[z]! != (M[j]!)[z]!)

@[expose] def r3CheckG (PT : ℕ → Array ℕ) (US : Array (Array ℕ)) (T : Array (Array ℕ)) : Bool :=
  eqA 120 T[0]! (idA 120) &&
    allLt T.size (fun i => !(US.all fun s => stabB s (maskOfG 120 PT T[i]!)) || i == 0)

@[expose] def adjTabG (n : ℕ) (S : Array (Array ℕ)) (D : UCls) : Array (Array Bool) :=
  let T := membersTabW D
  Array.ofFn (n := nClsW D) fun c => Array.ofFn (n := nClsW D) fun c' =>
    (T.getD c []).all fun i => (T.getD c' []).all fun i' =>
      eqA n (compA n (S.getD i #[]) (S.getD i' #[])) (compA n (S.getD i' #[]) (S.getD i #[]))

@[expose] def okPreG (A : Array (Array Bool)) (d : List Bool) : Bool :=
  let adj := fun c c' => (A.getD c #[]).getD c' false
  let da := d.toArray
  match d.getLast? with
  | some true => adj (d.length - 1) (d.length - 1) &&
      allLt (d.length - 1) fun c' => !(da.getD c' false) || adj c' (d.length - 1)
  | _ => true

@[expose] def s5CheckG (n : ℕ) (US : Array (Array ℕ)) (UB : Array ℕ) (LS : Array (Array ℕ))
    (LB : Array ℕ) (a : Array ℕ) (cands : List (List ℤ)) (S : Array (Array ℕ)) (D : UCls) : Bool :=
  S.size == 4096 &&
    allLt 4096 (fun i => isInvA n (S.getD i #[]) (invCand n (S.getD i #[])) &&
      (S.getD i #[]).size == n && memG n US UB (S.getD i #[])) &&
    allLt 4096 (fun i => allLt i fun j => !eqA n (S.getD i #[]) (S.getD j #[])) &&
    allLt 4096 (fun i => match clsOfW D i with
      | none => !(isInvol n (S.getD i #[]))
      | some (c, j) => decide (c < nClsW D) && decide (j < 4096) && isInvol n (S.getD i #[]) &&
          eqA n (S.getD i #[]) (conjA n (S.getD j #[]) (S.getD (repOfW D c) #[]))) &&
    allLt (nClsW D) (fun c => decide (repOfW D c < 4096)) &&
    (enumAux (okPreG (adjTabG n S D)) (nClsW D) []).all fun d =>
      sumSelW D d != 63 || cands.any fun w =>
        let da := d.toArray
        let l := wordA n LS (rawInvs n LS) w
        memG n LS LB l && isInvA n l (invCand n l) && !eqA n (conjA n l a) a &&
          allLt 4096 fun i => !(selB da (clsOfW D i)) ||
            (let y := conjA n l (S.getD i #[])
             (List.range 4096).any fun k => eqA n y (S.getD k #[]) && selB da (clsOfW D k))

@[expose] def q3CheckG (uA : ℕ → Array ℕ) (US : Array (Array ℕ)) (PS : Array (Array ℕ))
    (PB : Array ℕ) (fA fB : Array Bool) (F : Array (Array ℕ)) (g8 : Array ℕ)
    (OS : Array (Array ℕ)) (uw : List (List ℤ)) (T : ℕ → Array ℕ) (U2 : Array (Array ℕ))
    (UB : Array ℕ) (tg : ℕ → Array ℕ) : Bool :=
  let fm := fun (A : Array Bool) (g : Array ℕ) =>
    (Array.ofFn (n := 120) fun z => A.getD (invCand 120 g)[z.val]! false : Array Bool)
  let MA := F.map (fm fA)
  let MB := F.map (fm fB)
  let rho2 := compA 360 g8 g8
  let ut := fun k => wordA 360 OS (rawInvs 360 OS) (uw.getD k [])
  let psi2 := fun j => T (2 ^ j)
  let sig := fun (lift : Array ℕ) => OmegaEight.copy0Arr (conjA 360 rho2 lift)
  allLt 6 (fun k => (uA k)[0]! == 0) &&
  F.size == 315 && eqA 120 F[0]! (idA 120) &&
  allLt F.size (fun j => isInvA 120 F[j]! (invCand 120 F[j]!) && memG 120 PS PB F[j]!) &&
  allLt F.size (fun j => allLt j fun j' => (List.range 120).any fun z =>
    (MA[j]!).getD z false != (MA[j']!).getD z false ||
      (MB[j]!).getD z false != (MB[j']!).getD z false) &&
  US.all (fun s => stabB s fA && stabB s fB) &&
  allLt F.size (fun j => !(US.all fun s => stabB s MA[j]! && stabB s MB[j]!) || j == 0) &&
  isInvA 360 rho2 (invCand 360 rho2) &&
  allLt 6 (fun k => eqA 120 (OmegaEight.copy0Arr (ut k)) (uA k) && memG 120 U2 UB (sig (ut k))) &&
  allLt 6 (fun j => eqA 120 (sig (psi2 j)) (tg j))

@[expose] def ListBind (n w : Nat) (T : Array (Array ℕ)) (TL m : Nat) : Prop :=
  T.size = m ∧ ∀ i < m, T[i]! = unpack n w (perAt n w TL i)

@[expose] def decCls (e : ℕ) : Option (ℕ × ℕ) := if e = 0 then none else some (e % 128 - 1, e / 128)

@[expose] noncomputable def uListK (n w : Nat) (cU : ChainT) : Array (Array ℕ) :=
  Array.ofFn (n := 4096) fun i => unpack n w (elemT n w cU i.val)

@[expose] noncomputable def uClsK (CLS REPS NC : Nat) : UCls :=
  ⟨Array.ofFn (n := 4096) fun i => decCls (clsAt CLS i.val),
    Array.ofFn (n := NC) fun c => fget REPS c.val 12⟩

end CFSG.KC.O8

end
