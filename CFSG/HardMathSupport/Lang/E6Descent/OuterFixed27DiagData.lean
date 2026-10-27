module

public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagK

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Lattice

namespace DiagWeyl

@[expose] def genA : List (List ℤ) := [[-1, 0, 0, 1, -1, 0], [-2, 0, 1, 0, 0, 0], [-2, 0, 0, 1, -1, 1], [-3, 0, 0, 1, 0, 0], [-2, 0, 0, 1, 0, 0], [-1, 1, 0, 0, 0, 0]]
@[expose] def genB : List (List ℤ) := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, -1, 1, 0], [0, 1, 1, -1, 1, -1], [0, 1, 1, -1, 0, 0]]
@[expose] def genAinv : List (List ℤ) := [[0, 0, 0, -1, 1, 0], [0, 0, 0, -1, 1, 1], [0, 1, 0, -2, 2, 0], [0, 0, 0, -2, 3, 0], [-1, 0, 0, -1, 2, 0], [-1, 0, 1, -1, 1, 0]]
@[expose] def genBinv : List (List ℤ) := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, -1], [0, 0, 0, 1, 0, -1], [0, 0, 0, 1, -1, 0]]

@[expose] def dWords : List (List Bool) := [[], [false], [true], [false, false], [false, true], [true, false], [true, true], [false, false, true], [false, true, false], [false, true, true], [true, false, false], [true, false, true], [true, true, false], [false, false, true, false], [false, false, true, true], [false, true, false, false], [false, true, false, true], [false, true, true, false], [true, false, false, true], [true, false, true, false], [true, false, true, true], [true, true, false, false], [true, true, false, true], [false, false, true, false, false], [false, false, true, false, true], [false, false, true, true, false], [false, true, false, false, true], [false, true, false, true, false], [false, true, false, true, true], [false, true, true, false, false], [false, true, true, false, true], [true, false, false, true, true], [true, false, true, false, true], [true, false, true, true, false], [true, true, false, false, true], [true, true, false, true, false], [true, true, false, true, true], [false, false, true, false, false, true], [false, false, true, false, true, false], [false, false, true, false, true, true], [false, false, true, true, false, false], [false, false, true, true, false, true], [false, true, false, false, true, true], [false, true, false, true, false, true], [false, true, false, true, true, false], [false, true, true, false, false, true], [false, true, true, false, true, false], [false, true, true, false, true, true], [true, false, true, false, true, true], [true, false, true, true, false, true], [true, true, false, false, true, true], [true, true, false, true, false, true], [true, true, false, true, true, false], [false, false, true, false, false, true, true], [false, false, true, false, true, false, true], [false, false, true, false, true, true, false], [false, false, true, true, false, false, true], [false, false, true, true, false, true, false], [false, false, true, true, false, true, true], [false, true, false, true, false, true, true], [false, true, false, true, true, false, true], [false, true, true, false, false, true, true], [false, true, true, false, true, false, true], [false, true, true, false, true, true, false], [true, false, true, true, false, true, true], [true, true, false, true, false, true, true], [true, true, false, true, true, false, true], [false, false, true, false, true, false, true, true], [false, false, true, false, true, true, false, true], [false, false, true, true, false, false, true, true], [false, false, true, true, false, true, false, true], [false, false, true, true, false, true, true, false], [false, true, false, true, true, false, true, true], [false, true, true, false, true, false, true, true], [false, true, true, false, true, true, false, true], [true, true, false, true, true, false, true, true], [false, false, true, false, true, true, false, true, true], [false, false, true, true, false, true, false, true, true], [false, false, true, true, false, true, true, false, true], [false, true, true, false, true, true, false, true, true], [false, false, true, true, false, true, true, false, true, true]]

@[expose] def dEval (ω : List Bool) : List (List ℤ) :=
  ω.foldl (fun M b => lmul 6 M (if b then genB else genA)) (lid 6)

@[expose] def dMats : List (List (List ℤ)) := dWords.map dEval

@[expose] def vecs3 : List (List ℤ) := (List.range 729).map fun n =>
  [(n % 3 : ℕ), (n / 3 % 3 : ℕ), (n / 9 % 3 : ℕ), (n / 27 % 3 : ℕ), (n / 81 % 3 : ℕ),
    (n / 243 % 3 : ℕ)].map (fun x : ℕ => (x : ℤ))

@[expose] def fixCount (M : List (List ℤ)) : ℕ :=
  (vecs3.filter fun u => (lmulVecT 6 M u).map (fun x => x % 3) = u).length

theorem dMats_length : dMats.length = 81 := by decide +kernel

theorem dMats_nodup : dMats.Nodup := by decide +kernel

theorem dMats_closed : ∀ M ∈ dMats, lmul 6 M genA ∈ dMats ∧ lmul 6 M genAinv ∈ dMats ∧
    lmul 6 M genB ∈ dMats ∧ lmul 6 M genBinv ∈ dMats := by decide +kernel

theorem dMats_fix : ∀ M ∈ dMats,
    (∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j) →
    27 ≤ fixCount M ∧ ((∀ i j : Fin 6, lget M i j = lget (lid 6) i j) → 81 ≤ fixCount M) := by
  have hall : DiagWeylK.allL DiagWeylK.chk dMats = true := by decide +kernel
  intro M hM h3
  have hf : fixCount M = DiagWeylK.fixCnt M := DiagWeylK.fixCnt_eq M
  rw [hf]
  exact DiagWeylK.chk_spec M (DiagWeylK.allL_spec _ _ hall M hM) h3

theorem dMats_inj : ∀ M ∈ dMats, ∀ M' ∈ dMats,
    (∀ i j : Fin 6, lget M i j = lget M' i j) → M = M' := by decide +kernel

theorem lid_mem_dMats : lid 6 ∈ dMats := by decide +kernel

theorem vecs3_nodup : vecs3.Nodup := by
  unfold vecs3
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb h
  rw [List.mem_range] at ha hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Nat.cast_inj] at h
  omega

end DiagWeyl

end CFSG.HardMathSupport.Lang.E6Descent
