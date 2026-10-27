module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U

@[expose] def q16FreeAt (es : Array (List ℕ)) (x : List ℕ) : Bool :=
  let x4 := sq14 (sq14 x)
  x4 == one14 || sq14 x4 != one14 ||
    allCheck (fun y => sq14 y != x4 || mul14 (mul14 x y) x != y) es

@[expose] def q16Free (es : Array (List ℕ)) : Bool :=
  allCheck (q16FreeAt es) es

end CFSG.CGT.PushingUpLit.SolKNA
