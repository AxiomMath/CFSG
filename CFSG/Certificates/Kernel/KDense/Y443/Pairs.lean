
module

public import CFSG.YGroups.Y443.Native.BrayWords
public import CFSG.YGroups.Y443.Native.CoverFactsWords
public import CFSG.YGroups.Y443.Native.OrderRelInputs
public import CFSG.YGroups.Y443.Native.PairRelAInputs
public import CFSG.YGroups.Y443.Native.PairRelBInputs
public import CFSG.YGroups.Y443.Native.PairRelCInputs
public import CFSG.YGroups.Y443.Native.PairRelDInputs
public import CFSG.YGroups.Y443.Native.Parabolic2Words
public import CFSG.YGroups.Y443.Native.Swap13Word

public section

namespace CFSG.KC.KDense.Y443

open CFSG.Monster.AxisCount CFSG.YGroups.Y443

@[expose] noncomputable def words (l : List (List Native.Gen × List Native.Gen)) (s : Nat) : List Native.Gen :=
  List.rec (motive := fun _ => Nat → List Native.Gen) (fun _ => List.nil)
    (fun p _ ih k => Nat.rec (motive := fun _ => List Native.Gen)
      (Prod.rec (motive := fun _ => List Native.Gen) (fun w₁ w₂ =>
        Bool.rec (motive := fun _ => List Native.Gen) w₁ w₂ (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1))) p)
      (fun j _ => ih j) k) l (Nat.shiftRight s (nat_lit 1))

@[expose] def fix3 (ws : List (List Native.Gen)) : List (List Native.Gen × List Native.Gen) :=
  let l := ws.map fun w => (w, [])
  l ++ l ++ l

@[expose] def p10115 : List (List Native.Gen × List Native.Gen) := fix3 orderWords
@[expose] def p10116 : List (List Native.Gen × List Native.Gen) := fix3 pairAWords
@[expose] def p10117 : List (List Native.Gen × List Native.Gen) := fix3 pairBWords
@[expose] def p10118 : List (List Native.Gen × List Native.Gen) := fix3 pairCWords
@[expose] def p10119 : List (List Native.Gen × List Native.Gen) := fix3 pairDWords
@[expose] def p10123 : List (List Native.Gen × List Native.Gen) := fix3 [spiderWord]

@[expose] def pAlign : List (List Native.Gen × List Native.Gen) := [(wcWord ++ omegaWord, omegaWord ++ tWord)]

@[expose] def p10111 : List (List Native.Gen × List Native.Gen) :=
  let l := [(omegaWord ++ kWord, eWord ++ omegaWord), (gWord, xWord ++ kWord ++ xWord ++ kWord),
    (xWord ++ gWord, gWord ++ xWord)]
  l ++ l ++ l ++ [(tWord ++ gWord, gWord ++ tWord), (tWord ++ gWord, gWord ++ tWord ++ xWord)]

@[expose] def pCover : List (List Native.Gen × List Native.Gen) :=
  [(EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord, omegaWord ++ coverPHat), (powL 3 coverPHat, []),
    (coverQ ++ omegaWord, omegaWord ++ coverQHat), (coverQHat ++ coverPHat ++ coverWy, coverWy ++ tWord)]

@[expose] def pP2 : List (List Native.Gen × List Native.Gen) :=
  [(rhoWord ++ rhoWord, [])] ++ rhoGens.map (fun t => (Lw t ++ rhoWord, rhoWord ++ Lw (armSwapL t))) ++
    [(omegaWord ++ mWord, rhoWord ++ omegaWord), (zmWord ++ qWord, qWord ++ tWord)]

@[expose] def pSwap : List (List Native.Gen × List Native.Gen) :=
  [(tWord ++ swap13Word, swap13Word ++ tWord), (mtmWord ++ swap13Word, swap13Word ++ zmWord)]

@[expose] def p9356 : List (List Native.Gen × List Native.Gen) := [(EdgeNoncomm.edgeWord, [])]

end CFSG.KC.KDense.Y443

end
