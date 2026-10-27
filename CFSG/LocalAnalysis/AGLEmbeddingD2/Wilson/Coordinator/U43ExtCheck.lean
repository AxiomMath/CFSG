module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43PairCheck

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] def extOK (t : ℕ) : Bool :=
  !(isOrd3 t) || [one4, zc, zc2].contains (uAt t) ||
    (let e := e9Elems zc (uAt t)
     (List.range 729).any fun s =>
       isOrd3Arr.getD s false && commutes4 (uAt s) (uAt t) && !(e.contains (uAt s)))

set_option compiler.extract_closed false in
@[noinline, expose] def uExtCheck : Bool :=
  (List.range 729).all extOK

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43
