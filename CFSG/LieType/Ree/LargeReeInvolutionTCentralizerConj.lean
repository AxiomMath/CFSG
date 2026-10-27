module

public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover

section Six

variable (K : Type) [Field K]

@[expose] def tSix
    (lam mu p p' r r' : K) : ModGL F4.tag K :=
  sylowX K 41 lam * sylowX K 45 mu * sylowX K 43 p * sylowX K 46 p' * sylowX K 44 r *
    sylowX K 47 r'

end Six

@[expose] def tPairWord : Word :=
  [(41, [[24]]), (45, [[25]])]

@[expose] def tConjWord : Word :=
  [(43, [[1, 24]]), (46, [[13, 25]]), (44, [[0, 1, 24], [3, 24]]), (47, [[12, 13, 25], [15, 25]])]

@[expose] def vtCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[2]],
   [[3, 13], [5]],
   [[1, 1, 13], [14]],
   [[2, 3], [9]],
   [[3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[2, 5, 12], [9, 12, 13], [9, 15], [11], [24]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[2, 3, 5, 12], [2, 12, 19], [3, 9, 12, 13], [4, 9], [5, 9, 12], [7, 19], [8]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23], [25]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [15, 17, 19], [20]]]

theorem vtCoords_check : collectCheck 6000 (sylowWord ++ tPairWord) vtCoords = true := by
  decide +kernel

theorem tvCoords_check :
    collectCheck 6000 (tPairWord ++ tConjWord ++ sylowWord) vtCoords = true := by
  decide +kernel

section Conj

variable {m : ℕ} {K : Type} [Field K]

@[expose] def coordValPQ (m : ℕ) (a b c d e f g h i j k l p q : K) : ℕ → K
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | 6 => g
  | 7 => h
  | 8 => i
  | 9 => j
  | 10 => k
  | 11 => l
  | 12 => largeReeSigma m a
  | 13 => largeReeSigma m b
  | 14 => largeReeSigma m c
  | 15 => largeReeSigma m d
  | 16 => largeReeSigma m e
  | 17 => largeReeSigma m f
  | 18 => largeReeSigma m g
  | 19 => largeReeSigma m h
  | 20 => largeReeSigma m i
  | 21 => largeReeSigma m j
  | 22 => largeReeSigma m k
  | 23 => largeReeSigma m l
  | 24 => p
  | 25 => q
  | _ => 0

theorem sylowV_eq_wordEvalPQ
    (a b c d e f g h i j k l p q : K) :
    sylowV m K a b c d e f g h i j k l =
      wordEval K (coordValPQ m a b c d e f g h i j k l p q) sylowWord := by
  simp only [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
    sylowX, wordEval, sylowWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, add_zero, coordValPQ, mul_assoc]
  ring_nf

variable [CharP K F4.prime]

theorem sylowV_conj_tPair
    (a b c d e f g h i j k l lam mu : K) :
    sylowV m K a b c d e f g h i j k l * (sylowX K 41 lam * sylowX K 45 mu) *
        (sylowV m K a b c d e f g h i j k l)⁻¹ =
      tSix K lam mu (b * lam) (largeReeSigma m b * mu) (d * lam + a * b * lam)
        (largeReeSigma m d * mu + largeReeSigma m a * largeReeSigma m b * mu) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set y := coordValPQ m a b c d e f g h i j k l lam mu with hy
  have h1 : sylowV m K a b c d e f g h i j k l * (sylowX K 41 lam * sylowX K 45 mu) =
      wordEval K y (sylowWord ++ tPairWord) := by
    rw [wordEval_append, ← sylowV_eq_wordEvalPQ]
    simp [wordEval, tPairWord, sylowX, polyEval, monoEval, hy, coordValPQ]
  have h2 : tSix K lam mu (b * lam) (largeReeSigma m b * mu) (d * lam + a * b * lam)
        (largeReeSigma m d * mu + largeReeSigma m a * largeReeSigma m b * mu) *
          sylowV m K a b c d e f g h i j k l =
      wordEval K y (tPairWord ++ tConjWord ++ sylowWord) := by
    rw [wordEval_append, wordEval_append, ← sylowV_eq_wordEvalPQ]
    simp only [tSix, wordEval, tPairWord, tConjWord, sylowX, polyEval, monoEval, hy, coordValPQ,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil,
      mul_one, add_zero, mul_assoc]
    ring_nf
  have h3 := (wordEval_of_collectCheck vtCoords_check y).trans
    (wordEval_of_collectCheck tvCoords_check y).symm
  rw [← h1, ← h2] at h3
  rw [h3]
  group

end Conj

end CFSG.LieType.Ree.LargeReeInvolution
