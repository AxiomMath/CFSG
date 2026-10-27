module

public import Certificates.Data.Kernel.SporSch.F2Mat
public import Certificates.Data.CFSGNative.J3.Check
import CFSG.Certificates.Kernel.SporSch.F2PayRun
import CFSG.Certificates.Kernel.Spor.J3SubSound
import CFSG.Certificates.Kernel.Spor.J3SortSound
public import Aesop.BuiltinRules
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.TBfsSound
public import Certificates.Data.Kernel.Spor.PChain
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KS.J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.TBfs CFSG.Perm.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.J3.Native

theorem payRun_eq (d : Nat) (cs : List Char) :
    rowsOfPayload d (String.ofList cs) = CFSG.KS.Raw.unpack d d (CFSG.KS.SporSch.payRun d cs 0 0 0) :=
  CFSG.KS.SporSch.F2P.payRun_rowsJ3 d cs

theorem sorted_sound {d n : Nat} {cA cB : Array Nat} {v0 : Nat} {PL TA TB BO BOI BQ : Nat → Nat}
    (hn : 0 < n ∧ n < 2 ^ 30)
    (hinc : ∀ i, i + 1 < n → PL i < PL (i + 1))
    (hpt : ∀ i < n, PL i < 2 ^ d ∧ TA i < n ∧ TB i < n ∧ vecMulN d cA (PL i) = PL (TA i) ∧
      vecMulN d cB (PL i) = PL (TB i))
    (hroot : BO 0 < n ∧ PL (BO 0) = v0)
    (hbo : ∀ i < n, BOI i < n ∧ BO (BOI i) = i)
    (hbfs : ∀ k < n, 0 < k → BO k < n ∧ BQ k < k ∧
      (BO k = TA (BO (BQ k)) ∨ BO k = TB (BO (BQ k)))) :
    orbitSorted d cA cB v0 n = Array.ofFn (n := n) (fun i => PL i.val) ∧
      imageTable d (posMap (Array.ofFn (n := n) fun i => PL i.val))
        (Array.ofFn (n := n) fun i => PL i.val) cA =
          Array.ofFn (n := n) (fun i => UInt32.ofNat (TA i.val)) ∧
      imageTable d (posMap (Array.ofFn (n := n) fun i => PL i.val))
        (Array.ofFn (n := n) fun i => PL i.val) cB =
          Array.ofFn (n := n) (fun i => UInt32.ofNat (TB i.val)) :=
  J3Sort.orbit_core hn.1 hinc (fun i hi => (hpt i hi).2) hroot hbo hbfs

@[expose] noncomputable def der3Step (n k : Nat) (L : Nat → Nat → Nat) (LBL REP PAR0 LAB0 POS0 : Nat → Nat)
    (D : Nat) (s : Nat × Nat) : Nat :=
  if s.1 < k ∧ s.2 < n ∧ D.testBit s.1 ∧ D.testBit (LBL s.2) then
    D ||| (1 <<< LBL ((walkInvK L PAR0 LAB0 (r32 POS0 (REP s.1)) [s.2]).getD 0 0))
  else D

@[expose] noncomputable def derK3 (n k : Nat) (L : Nat → Nat → Nat) (LBL REP PAR0 LAB0 POS0 : Nat → Nat)
    (c : Nat) (steps : List (Nat × Nat)) : Bool :=
  steps.foldl (der3Step n k L LBL REP PAR0 LAB0 POS0) ((1 <<< 0) ||| (1 <<< c)) == 2 ^ k - 1

theorem j3sub_sound {NL k cnt0 : Nat} (D : Data) {letters : Array Table} {lv : Array Nat}
    {L : Nat → Nat → Nat} {B : Nat → Nat} {PTS0 POS0 PAR0 LAB0 LBL REP SCNT : Nat → Nat}
    {SPTS SPOS SPAR SLAB STI : Nat → Nat → Nat}
    (hL : letters.size = NL ∧ ∀ l < NL, ∀ x < D.n, ap letters[l]! x = L l x ∧ L l x < D.n)
    (hlv : lv = (lvK L B NL 1).toArray)
    (hb : 0 < D.base.size ∧ D.base[0]! = 0)
    (hk : D.subReps.size = k ∧ 0 < k ∧ D.derivs.size = k ∧ ∀ l < k, D.subReps[l]! = REP l)
    (hr0 : REP 0 = 0 ∧ SCNT 0 = 1)
    (hT0 : ∀ l < k, r32 POS0 (REP l) < cnt0 ∧ r32 PTS0 (r32 POS0 (REP l)) = REP l)
    (hl0 : ∀ q < cnt0, 0 < q → invL (r32 LAB0 q) < NL)
    (hs : ∀ l < k, tbfsHdK D.n (REP l) (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l) = true ∧
      ∀ q < SCNT l, tbfsPtK D.n (SCNT l) (lvK L B NL 1).length L (lvAt L B NL 1) (SPTS l) (SPOS l)
        (SPAR l) (SLAB l) (STI l) q = true)
    (hz : ∀ z < D.n, LBL z < k ∧ r32 (SPOS (LBL z)) z < SCNT (LBL z) ∧
      r32 (SPTS (LBL z)) (r32 (SPOS (LBL z)) z) = z)
    (hq : ∀ l < k, ∀ q < SCNT l, LBL (r32 (SPTS l) q) = l)
    (hd : ∀ c, 1 ≤ c → c < k → derK3 D.n k L LBL REP PAR0 LAB0 POS0 c D.derivs[c]! =
      true) :
    subChecks D letters lv (D.subReps.map fun r => treeBFS D.n r letters lv)
        (labelsOf D.n (D.subReps.map fun r => treeBFS D.n r letters lv)) = true ∧
      derivChecks D letters (tbfsRec D.n cnt0 PTS0 POS0 PAR0 LAB0)
        (labelsOf D.n (D.subReps.map fun r => treeBFS D.n r letters lv)) = true :=
  J3Sub.j3sub_core D hL hlv hb hk hr0 hT0 hl0 hs hz hq (fun _ _ => rfl)
    (fun c h1 h2 => beq_iff_eq.1 (hd c h1 h2))

end CFSG.KS.J3S

end
