module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Base
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
import CFSG.Mathlib.Decide.FinFun
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def rr5 (l : List ℤ) : List ℤ := e5Rows.map fun e => dotZ e l % 5

@[expose] def pivot5 (fl : List ℤ) : ℕ :=
  ((List.range fl.length).find? fun i => fl.getD i 0 != 0).getD 0

@[expose] def key5 (fl : List ℤ) (g : List ℤ) : List ℤ :=
  List.zipWith (fun a b => (a - g.getD (pivot5 fl) 0 * b) % 5) g fl

@[expose] def fib5 (fl : List ℤ) (l : List ℤ) : List ℤ := key5 fl (rr5 l)

@[expose] def rootsN5 : List (List ℤ × ℤ) :=
  Tag.E8.artifactRoots.map fun l => (l, formB (gramL Tag.E8) l l)

@[expose] def fibRootsG (fib : List ℤ → List ℤ) (RN : List (List ℤ × ℤ)) :
    List (List ℤ × ℤ × List ℤ) :=
  RN.map fun p => (p.1, p.2, fib p.1)

@[expose] def matVecL (M : List (List ℤ)) (v : List ℤ) : List ℤ := M.map fun row => dotZ row v

@[expose] def famOK5 (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (M : List (List ℤ)) (fl : List ℤ) : Bool :=
  let FR := fibRootsG (fib5 fl) RN
  let T := tuplesL B FR E (E.map (fib5 fl)) NE
  let K := kerRootsL FR (List.replicate 4 0)
  if K.isEmpty then T.all (· == E) else
    K.any fun α =>
      (K.all fun x => x == α || x == α.map (- ·) || x == matVecL M α ||
          x == (matVecL M α).map (- ·)) &&
        K.contains (α.map (- ·)) && K.contains (matVecL M α) &&
        K.contains ((matVecL M α).map (- ·)) &&
        T.all fun t => t == E || t == E.map (reflB B α) || t == E.map (reflB B (matVecL M α)) ||
          t == (E.map (reflB B (matVecL M α))).map (reflB B α)

@[expose] def allF5 : List (List ℤ) :=
  (List.range 5).flatMap fun a => (List.range 5).flatMap fun b =>
    (List.range 5).flatMap fun c => (List.range 5).filterMap fun d =>
      let f : List ℤ := [a, b, c, d]
      if f.all (· == 0) || f.getD (pivot5 f) 0 == 1 then some f else none

private theorem famOK5_all_0 : ((allF5.drop (0 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_1 : ((allF5.drop (1 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_2 : ((allF5.drop (2 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_3 : ((allF5.drop (3 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_4 : ((allF5.drop (4 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_5 : ((allF5.drop (5 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_6 : ((allF5.drop (6 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_7 : ((allF5.drop (7 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_8 : ((allF5.drop (8 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

private theorem famOK5_all_9 : ((allF5.drop (9 * 16)).take 16).all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true := by
  decide +kernel

theorem famOK5_all : allF5.all (famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
    ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat) = true :=
  CFSG.Decide.FinFun.all_of_chunks 16 10 _ (by decide +kernel) fun k hk => by
    interval_cases k
    exacts [famOK5_all_0, famOK5_all_1, famOK5_all_2, famOK5_all_3, famOK5_all_4, famOK5_all_5,
      famOK5_all_6, famOK5_all_7, famOK5_all_8, famOK5_all_9]

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
