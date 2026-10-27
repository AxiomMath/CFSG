module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowData

public section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Monster.B.Co2.Native

section Checks

open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover (arrTable)

@[expose] def treeLitCheck : Bool := treeOK treeLit.1 treeLit.2.1 treeLit.2.2

@[expose] def sylowRepsLitCheck : Bool :=
  repArrs.all (fun r => ordTest 360 2 (arrTable 360 r)) &&
    (List.range 38).all fun j =>
      siftA 360 (rawLevels 360 omegaS (omegaBase.map Fin.val).toArray)
          (omegaBase.map Fin.val).toArray 0 (repArrs.getD j #[]) ==
        decide (repTypes.getD j 0 < 3) &&
      eqA 360 (conjArr (conjArrs.getD j #[]) (mainArrs.getD (repTypes.getD j 0) #[]))
        (repArrs.getD j #[])

end Checks

@[expose] def matApp (M v : ℕ) : ℕ :=
  (List.range 8).foldr (fun c acc => if v.testBit c then (M / 256 ^ c % 256) ^^^ acc else acc) 0

@[expose] def matMulM (A B : ℕ) : ℕ :=
  (List.range 8).foldr (fun c acc => matApp A (B / 256 ^ c % 256) + 256 * acc) 0

@[expose] def idCode : ℕ := (List.range 8).foldr (fun c acc => 2 ^ c + 256 * acc) 0

@[expose] def ActsOn0 (t : Array ℕ) (M : ℕ) : Prop :=
  ∀ p < 120, t[p]! < 120 ∧ t[p]! = nsIdx[matApp M nsArr[p]!]!

@[expose] def saMat (i : ℕ) : ℕ := saCodes / 2 ^ (64 * i) % 2 ^ 64

@[expose] def saMul (i l : ℕ) : ℕ := saMulT / 2 ^ (13 * (5 * i + l)) % 8192

@[expose] def saPar (i : ℕ) : ℕ := saParT / 2 ^ (13 * i) % 8192

@[expose] def saLab (i : ℕ) : ℕ := saLabT / 2 ^ (3 * i) % 8

@[expose] def saGen (l : ℕ) : ℕ := saGenT / 2 ^ (13 * l) % 8192

@[expose] def yIdx (j : ℕ) : ℕ := yIdxT / 2 ^ (13 * j) % 8192

@[expose] def invW (i : ℕ) : ℕ × ℕ × ℕ :=
  (invWT / 2 ^ (32 * i + 26) % 64, invWT / 2 ^ (32 * i + 13) % 8192, invWT / 2 ^ (32 * i) % 8192)

@[expose] def rgCode (j l : ℕ) : ℕ := rgT / 2 ^ (64 * (5 * j + l)) % 2 ^ 64

@[expose] def rgInv (j l : ℕ) : ℕ := rgInvT / 2 ^ (64 * (5 * j + l)) % 2 ^ 64

@[expose] def conjW (G Gi : ℕ → ℕ) (w : List ℕ) (b : ℕ) : ℕ :=
  w.foldr (fun l acc => matMulM (matMulM (G l) acc) (Gi l)) b

@[expose] def rgConj (j : ℕ) (w : List ℕ) (b : ℕ) : ℕ := conjW (rgCode j) (rgInv j) w b

structure SAFacts : Prop where
  gens : ∀ l < 5, saGen l < 8192 ∧ ActsOn0 sylowGens[l]! (saMat (saGen l))
  id0 : saMat 0 = idCode
  closed : ∀ i < 8192, ∀ l < 5, matMulM (saMat (saGen l)) (saMat i) = saMat (saMul i l)
  tree : ∀ i < 8192, 0 < i → saPar i < i ∧ saLab i < 5 ∧ saMul (saPar i) (saLab i) = i
  distinct : ∀ i < 8192, ∀ k < 8192, saMat i = saMat k → i = k
  span : ∀ c < 8, spanA.getD c 0 < 256 ∧ spanB.getD c 0 < 256 ∧ qNat (spanA.getD c 0) = true ∧
    qNat (spanB.getD c 0) = true ∧ spanA.getD c 0 ^^^ spanB.getD c 0 = 2 ^ c
  reps : ∀ j < 38, yIdx j < 8192 ∧ ActsOn0 (repArrs.getD j #[]) (saMat (yIdx j))
  invol : ∀ i < 8192, i ≠ 0 → matMulM (saMat i) (saMat i) = idCode →
    (invW i).1 < 38 ∧ (invW i).2.1 < 8192 ∧ (invW i).2.2 < 8192 ∧
      matMulM (saMat (invW i).2.1) (saMat (invW i).2.2) = idCode ∧
      matMulM (matMulM (saMat (invW i).2.1) (saMat (yIdx (invW i).1))) (saMat (invW i).2.2) =
        saMat i
  rg : ∀ j < 38, ∀ l < (repGens j).length,
    ActsOn0 ((repGens j).getD l #[]) (rgCode j l) ∧
      ActsOn0 (invCand 360 ((repGens j).getD l #[])) (rgInv j l)
  five : ∀ j < 38, ∀ i < 8192, matMulM (saMat i) (saMat i) ≠ idCode →
    matMulM (matMulM (saMat i) (saMat i)) (matMulM (saMat i) (saMat i)) = idCode →
    matMulM (saMat i) (saMat (yIdx j)) = matMulM (saMat (yIdx j)) (saMat i) →
    ∃ ws : List (List ℕ), ws.length = 5 ∧ (∀ w ∈ ws, ∀ l ∈ w, l < (repGens j).length) ∧
      ws.Pairwise fun w w' => rgConj j w (saMat i) ≠ rgConj j w' (saMat i)

end CFSG.EvenSmallLie.OmegaEight

end
