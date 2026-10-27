module

public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
public import Certificates.Data.M13L33Rels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33

open CFSG.PSL3Four.Native CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsThree
open CFSG.HardMathSupport.Dickson.BMRows.M13L33 (l33Rels)

@[expose] def l33AWords : List (List Int) := [[4, 5, 4, 5, 3, -2], [4, -2, 1, -2, 6]]

@[expose] def l33BWords : List (List Int) := [[4, 5, 4, 3, 2], [-5, 6, 2, 3]]

@[expose] def letterWord (a b : List Int) (l : Fin 2 × Bool) : List Int :=
  cond l.2 (if l.1 = 0 then a else b) (invWord (if l.1 = 0 then a else b))

@[expose] def relWord (a b : List Int) (r : List (Fin 2 × Bool)) : List Int :=
  r.flatMap (letterWord a b)

@[expose] def l33CheckAt (k : Nat) : Bool :=
  let D := lLocalData k ()
  let a := l33AWords.getD k []
  let b := l33BWords.getD k []
  (l33Rels.all fun r => Certificates.MaxD2Perm.wT D (relWord a b r) == idTab D.n) &&
    !(Certificates.MaxD2Perm.wT D a == idTab D.n)

@[expose] def titsL33Check (_ : Unit := ()) : Bool := allBelow 2 l33CheckAt

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33
