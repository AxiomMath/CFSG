module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Data
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def rr17 (l : List ℤ) : List ℤ := e17Rows.map fun e => dotZ e l % 17

@[expose] def fam17OK (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) : Bool :=
  let FR := fibRootsG rr17 RN
  let T := tuplesL B FR E (E.map rr17) NE
  (kerRootsL FR (List.replicate 2 0)).isEmpty && T.all (· == E)

theorem fam17_ok : fam17OK (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) = true := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
