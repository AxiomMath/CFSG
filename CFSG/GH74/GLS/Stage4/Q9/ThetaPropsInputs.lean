module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaModel
public import CFSG.GH74.GLS.Stage4.Q9.FrobCount
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import CFSG.GH74.GLS.Stage4.Q9.ChatOrders
public meta import CFSG.GH74.GLS.Stage4.Q9.Tables
public meta import Mathlib

@[expose] public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG Subgroup
namespace ThetaProps

structure LTyp where
  inner : Bool
  ord : ℕ
  mu : Bool
  ridx : Fin 7
  deriving DecidableEq

def typ (l : Lg) : LTyp :=
  ⟨decide (parityL l = 1), ordL l, decide (muFlag l), if parityL l = 1 then repIdx l.left else 0⟩

def typTab : List (LTyp × ℕ) :=
  [(⟨true, 1, false, 0⟩, 1), (⟨true, 2, true, 0⟩, 1),
   (⟨true, 3, false, 1⟩, 40), (⟨true, 6, true, 1⟩, 40),
   (⟨true, 3, false, 2⟩, 40), (⟨true, 6, true, 2⟩, 40),
   (⟨true, 4, true, 3⟩, 90), (⟨true, 8, true, 4⟩, 180),
   (⟨true, 5, false, 5⟩, 72), (⟨true, 10, true, 5⟩, 72),
   (⟨true, 5, false, 6⟩, 72), (⟨true, 10, true, 6⟩, 72),
   (⟨false, 2, false, 0⟩, 72), (⟨false, 10, false, 0⟩, 288), (⟨false, 16, true, 0⟩, 360)]

def typList : List LTyp := typTab.map Prod.fst

def typCountsOK : Bool :=
  let tl : Multiset LTyp := (Finset.univ : Finset Lg).val.map typ
  typTab.all fun p => decide (tl.count p.1 = p.2)

end ThetaProps

open ThetaProps
end CFSG.GH74.GLS.Stage4.Q9
