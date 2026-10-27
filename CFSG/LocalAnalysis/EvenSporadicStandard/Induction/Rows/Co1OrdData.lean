module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.Co1Ord

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Blueprint
open scoped Matrix

@[expose] def co1OrdProg : List Instr :=
  [.iv 2 3, .mu 1 3 4, .mu 4 4 5, .mu 5 5 6, .mu 6 4 7, .mu 1 2 8, .mu 7 8 9, .mu 9 4 10]

@[expose] def co1OrdOut : ℕ := 10

@[expose] def co1OrdRegs (_ : Unit := ()) : Array (Array ℕ × Array ℕ) :=
  runProgN (ops2 24) (initRegsN (ops2 24) 11
    ((ops2 24).decode NativeSporadic.Co1Seed1, (ops2 24).decode NativeSporadic.Co1Seed1)
    ((ops2 24).decode NativeSporadic.Co1Seed2,
      (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2)) co1OrdProg

@[expose] def co1OrdCheck (_ : Unit := ()) : Bool :=
  co1OrdProg.all (Instr.lt 11) &&
    (ops2 24).eq ((ops2 24).pow (co1OrdRegs ())[co1OrdOut]!.1 16) (ops2 24).one &&
    (ops2 24).vne ((ops2 24).vmul ((ops2 24).unit 0)
      ((ops2 24).pow (co1OrdRegs ())[co1OrdOut]!.1 8)) ((ops2 24).unit 0)

end CFSG.EvenSporadicStandard.Induction.Co1Ord
