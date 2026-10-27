module

public import CFSG.HardMathSupport.Foote.E27.LieThree.CommFast
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpData
public meta import CFSG.HardMathSupport.Foote.E27.LieThree.CommFast
public meta import CFSG.HardMathSupport.Foote.E27.LieTwo.SpData

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.Sporadic.He.Native

@[expose] def sp63Gens : Array AM :=
  #[#[#[1, 1, 0, 0, 0, 0], #[0, 1, 0, 0, 0, 0], #[0, 0, 1, 0, 0, 0], #[0, 0, 0, 1, 0, 0],
      #[0, 0, 0, 2, 1, 0], #[0, 0, 0, 0, 0, 1]],
    #[#[1, 0, 0, 0, 0, 0], #[0, 1, 1, 0, 0, 0], #[0, 0, 1, 0, 0, 0], #[0, 0, 0, 1, 0, 0],
      #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 2, 1]],
    #[#[1, 0, 0, 0, 0, 0], #[0, 1, 0, 0, 0, 0], #[0, 0, 1, 0, 0, 1], #[0, 0, 0, 1, 0, 0],
      #[0, 0, 0, 0, 1, 0], #[0, 0, 0, 0, 0, 1]]]

@[expose] def sp63Pos : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (2, 3), (2, 4), (2, 5), (1, 3), (1, 4), (0, 3)]

@[expose] def sp63Tab (_ : Unit := ()) : RawTab := buildTabH 3 6 sp63Gens 20000

@[expose] def sp63Check (_ : Unit := ()) : Bool :=
  sp63Gens.all (symplAP 3 3) && tabOKP 3 6 sp63Pos sp63Gens (sp63Tab ()) &&
    ((sp63Tab ()).elts.size == 19683) && commOKc (candIdx (fun _ => true) (sp63Tab ())) (sp63Tab ())

end CFSG.HardMathSupport.Foote.E27
