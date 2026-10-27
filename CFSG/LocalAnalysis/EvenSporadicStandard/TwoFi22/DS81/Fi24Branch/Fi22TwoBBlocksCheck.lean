module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2.Native

@[expose] def blocks45 : List (List Nat) :=
  [[25, 426, 756, 2261],
   [660, 1797, 2887, 3237],
   [562, 714, 2427, 2922],
   [1678, 2143, 2542, 3046],
   [449, 497, 842, 1080],
   [495, 700, 1976, 2631],
   [435, 436, 998, 1680],
   [63, 244, 650, 1762],
   [572, 829, 2707, 3460],
   [345, 444, 603, 1681],
   [1925, 2313, 2483, 3416],
   [88, 1288, 1732, 2906],
   [432, 2899, 3009, 3297],
   [455, 2541, 2658, 2692],
   [464, 2034, 2863, 3165],
   [1161, 1922, 2495, 2841],
   [532, 741, 2555, 3217],
   [367, 1228, 1877, 1958],
   [75, 1881, 2386, 3475],
   [1451, 1621, 3004, 3350],
   [512, 1405, 2058, 3359],
   [883, 1131, 2023, 3175],
   [47, 1949, 2337, 3354],
   [863, 2085, 2845, 3343],
   [1357, 1550, 2629, 3154],
   [81, 755, 2102, 3030],
   [1798, 2607, 2875, 3202],
   [360, 1529, 2311, 2958],
   [359, 1036, 1295, 3045],
   [234, 679, 970, 1772],
   [356, 538, 838, 2973],
   [626, 1482, 3127, 3161],
   [819, 823, 1827, 3172],
   [1920, 2321, 2506, 2743],
   [1596, 2625, 2628, 3353],
   [72, 318, 1353, 1704],
   [99, 575, 995, 1570],
   [1033, 2501, 2620, 3446],
   [279, 1465, 2207, 2770],
   [1189, 1603, 1835, 2572],
   [1536, 2569, 2645, 2825],
   [2769, 3051, 3286, 3504],
   [1974, 2384, 2480, 2913],
   [30, 193, 1642, 2783],
   [490, 885, 1079, 1211]]

@[expose] def xyfArr : Array (Array Nat) :=
  #[#[0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17, 20, 23, 18, 21, 24,
      25, 26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41, 44],
    #[38, 0, 42, 18, 32, 13, 28, 10, 22, 8, 33, 17, 31, 19, 5, 34, 11, 25, 4, 23, 7, 30, 26, 14,
      21, 35, 39, 44, 1, 41, 2, 36, 40, 37, 43, 16, 27, 20, 6, 9, 3, 15, 24, 29, 12],
    #[0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 18, 17, 22, 24, 23, 19, 21, 20,
      35, 36, 38, 37, 42, 44, 43, 39, 41, 40, 25, 26, 28, 27, 32, 34, 33, 29, 31, 30]]

@[expose] def tauWords : List (List Int) :=
  [[],
   [-1, 2, 2, -3, -2, -2, -2, -1, -3, 2, 2, -1, -2, -1],
   [-1, -2, -1, 2, 2, 2, -1, -2, -1, -3, -2, -2, -1, 2, 2, -1, -2, -3, -2, -1],
   [3, 2, 3, 2, 2, -1, 2, -3, -2, -1, -3, 2, -1, 2, -1, 2, -3, 2, -3, -2, -3, -2, -3],
   [-1, -2, -3, 2, 2, -1, -2, -2, -1, 2, 2, -1, -2, -3, -2],
   [3, -2, -2, 3, -2, -2, -2, -1, -3, 2, 2, 3, 2, -1, 2, 2, -1, 2, 2, -1, -2, -3, -2, -1, 2, 2,
    -1, -2, -3, -2],
   [-2, -2, -1, -2, -3, -2, -2, -1, 2, -1, -2, -1, -3, -2, -2, -1, -2, -1, 2, 2, -1, -2, -3],
   [-1, -2, -2, 3, -2, 3, -2, -2, -2, -1, 2, 2, -1, -2, -3, -2, -1, 2, 2, -1, -2, -3, -2],
   [1, 2, 3, 2, 1, -2, -2, 1, 2, 2, -1, 2, -3, 2, -3, -2, -3, -2, -3, -2, -3, 2, -1, -3, 2, -3,
    -2],
   [-2, 3, 2, 2, -1, 2, 2, 3, 2, 3, -2, 3, -2, 1, -2, -2, -1, 2, 2, -1, -2, -3, -2]]

@[expose] def genWords : List (List Int) :=
  [[-9, 7, -2, 9, 10, -3, -3, -3],
   [-3, -3, -3, -3, -9, -9, 7, -2, -4, -10, -8, 4],
   [5, 3, -2, -10, 9, -10, -8, 10, 3, 3, 3, 3, 3]]

@[expose] def labelOf (p : Nat) : Nat := blocks45.findIdx fun b => b.contains p

@[expose] def labelArr (_ : Unit := ()) : Array Nat := Array.ofFn (n := 3510) fun p => labelOf p.val

@[expose] def extGet (T : Array Nat) (m : Nat) : Nat := if m < 45 then T[m]! else 45

@[expose] def tauArrs (_ : Unit := ()) : Array (Array Nat) :=
  let X := xyfArr
  let Xi := X.map (invCand 45)
  Array.ofFn (n := 10) fun k => wordA 45 X Xi (tauWords.getD k [])

@[expose] def checkBlocks (_ : Unit := ()) : Bool :=
  let X := xyfArr
  let Xi := X.map (invCand 45)
  let T := tauArrs ()
  let Ti := T.map (invCand 45)
  let lab := labelArr ()
  let S : Array (Array Nat) := Array.ofFn (n := 10) fun h => genArr h
  let Si : Array (Array Nat) := S.map (invCand 3510)
  let qa : Array (Array Nat) := Array.ofFn (n := 10) fun j => wordA 3510 S Si (qWords.getD j [])
  blocks45.length == 45 && tauWords.length == 10 && genWords.length == 3 && X.size == 3 &&
    tauWords.all (lettersOK 3) && genWords.all (lettersOK 10) && qWordsOK &&
    allLt 3 (fun j => isInvA 45 X[j]! Xi[j]!) &&
    allLt 10 (fun k => isInvA 45 T[k]! Ti[k]!) &&
    allLt 3 (fun j => eqA 45 (wordA 45 T Ti (genWords.getD j [])) X[j]!) &&
    allLt 45 (fun i => decide ((blocks45.getD i []).headD 0 < 3510) &&
      lab[(blocks45.getD i []).headD 0]! == i) &&
    allLt 10 (fun k => allLt 3510 fun p => lab[(S[k]!)[p]!]! == extGet T[k]! lab[p]!) &&
    allLt 3510 (fun p => lab[t1Arr[p]!]! == lab[p]!) &&
    allLt 10 (fun j => allLt 3510 fun p => lab[(qa[j]!)[p]!]! == lab[p]!)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
