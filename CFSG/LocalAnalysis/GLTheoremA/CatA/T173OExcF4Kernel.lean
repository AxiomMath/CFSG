module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4
public import CFSG.LocalAnalysis.SteinbergCEPfaffianFour

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

abbrev i0 : Fin Tag.F4.rank := ⟨0, by decide⟩
abbrev i1 : Fin Tag.F4.rank := ⟨1, by decide⟩

abbrev i2 : Fin Tag.F4.rank := ⟨2, by decide⟩

abbrev i3 : Fin Tag.F4.rank := ⟨3, by decide⟩

def dot4Z (x y : Fin Tag.F4.rank → ℤ) : ℤ := ∑ i, x i * y i

def det3Z (u v w : Fin 3 → ℤ) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) +
    u 2 * (v 0 * w 1 - v 1 * w 0)

def minorDetZ (a b c : Fin Tag.F4.rank → ℤ) (j : Fin Tag.F4.rank) : ℤ :=
  det3Z (fun k => a (Fin.succAbove j k)) (fun k => b (Fin.succAbove j k))
    (fun k => c (Fin.succAbove j k))

def cofactorZ (a b c : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  fun j => (-1 : ℤ) ^ j.val * minorDetZ a b c j

def f4LongRootsP : List ({x : Fin Tag.F4.rank → ℤ // IsLongRoot x}) :=
  [  ⟨(![0,1,0,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![0,1,0,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i0 * simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,1,2,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![0,1,2,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i0 * simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,1,2,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![0,1,2,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i2 * simple .F4 i0 * simple .F4 i1,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,0,0,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,0,0,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,0,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,1,0,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,2,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,1,2,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,2,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,1,2,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i2 * simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,2,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,2,2,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i1 * simple .F4 i2 * simple .F4 i1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,2,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,2,2,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i1 * simple .F4 i2 * simple .F4 i1,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,4,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,2,4,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i3 * simple .F4 i1 * simple .F4 i2 * simple .F4 i1,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,3,4,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![1,3,4,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i1 * simple .F4 i2 * simple .F4 i3 * simple .F4 i1 * simple .F4 i2 *
        simple .F4 i1,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![2,3,4,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i0 1) = (![2,3,4,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i0 * simple .F4 i1 * simple .F4 i2 * simple .F4 i3 * simple .F4 i1 *
        simple .F4 i2 * simple .F4 i1,
      by simp [mul_smul, simple_smul]; decide⟩⟩]

def f4ShortRootsP : List ({x : Fin Tag.F4.rank → ℤ // IsShortRoot x}) :=
  [  ⟨(![0,0,0,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,0,0,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨1, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,0,1,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,0,1,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,0,1,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,0,1,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,1,1,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,1,1,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i1 * simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,1,1,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,1,1,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i1 * simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![0,1,2,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![0,1,2,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i1 * simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,1,0] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,1,1,0] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i0 * simple .F4 i1 * simple .F4 i2,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,1,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,1,1,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i0 * simple .F4 i1 * simple .F4 i2, by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,1,2,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,1,2,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i0 * simple .F4 i1 * simple .F4 i2,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,2,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,2,2,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i1 * simple .F4 i2 * simple .F4 i0 * simple .F4 i1 * simple .F4 i2,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,3,1] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,2,3,1] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i2 * simple .F4 i1 * simple .F4 i2 * simple .F4 i0 * simple .F4 i1 *
        simple .F4 i2,
      by simp [mul_smul, simple_smul]; decide⟩⟩,
  ⟨(![1,2,3,2] : Fin Tag.F4.rank → ℤ), by
    change ∃ w : WeylGroup .F4, w • (Pi.single i3 1) = (![1,2,3,2] : Fin Tag.F4.rank → ℤ)
    exact ⟨simple .F4 i3 * simple .F4 i2 * simple .F4 i1 * simple .F4 i2 * simple .F4 i0 *
        simple .F4 i1 * simple .F4 i2,
      by simp [mul_smul, simple_smul]; decide⟩⟩]

abbrev toF4 (v : Fin 4 → ℤ) : Fin Tag.F4.rank → ℤ := fun i => v i

def f4PosRoots : List (Fin Tag.F4.rank → ℤ) :=
  [(toF4 ![0,1,0,0]),
   (toF4 ![0,1,2,0]),
   (toF4 ![0,1,2,2]),
   (toF4 ![1,0,0,0]),
   (toF4 ![1,1,0,0]),
   (toF4 ![1,1,2,0]),
   (toF4 ![1,1,2,2]),
   (toF4 ![1,2,2,0]),
   (toF4 ![1,2,2,2]),
   (toF4 ![1,2,4,2]),
   (toF4 ![1,3,4,2]),
   (toF4 ![2,3,4,2]),
   (toF4 ![0,0,0,1]),
   (toF4 ![0,0,1,0]),
   (toF4 ![0,0,1,1]),
   (toF4 ![0,1,1,0]),
   (toF4 ![0,1,1,1]),
   (toF4 ![0,1,2,1]),
   (toF4 ![1,1,1,0]),
   (toF4 ![1,1,1,1]),
   (toF4 ![1,1,2,1]),
   (toF4 ![1,2,2,1]),
   (toF4 ![1,2,3,1]),
   (toF4 ![1,2,3,2])]

theorem dot4Z_cofactorZ (x a b c : Fin Tag.F4.rank → ℤ) :
    dot4Z (cofactorZ a b c) x =
      (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) ℤ).det := by
  rw [CFSG.LocalAnalysis.det_four]
  change ∑ i : Fin 4, cofactorZ a b c i * x i = _
  simp [Fin.sum_univ_four, cofactorZ, minorDetZ, det3Z, Fin.succAbove]
  ring

def f4Indices : List (Fin Tag.F4.rank) := [i0, i1, i2, i3]

def allRoots : List (Fin Tag.F4.rank → ℤ) :=
  f4PosRoots ++ f4PosRoots.map fun v => -v

def memAllRoots (v : Fin Tag.F4.rank → ℤ) : Bool :=
  allRoots.any fun w => w == v

def closedCheck : Bool :=
  allRoots.all fun v => f4Indices.all fun i => memAllRoots (reflect .F4 i v)

def simpleCheck : Bool :=
  f4Indices.all fun i => memAllRoots (Pi.single i 1)

lemma memAllRoots_eq_true {v : Fin Tag.F4.rank → ℤ} :
    memAllRoots v = true ↔ v ∈ allRoots := by
  simp [memAllRoots, List.any_eq_true, beq_iff_eq]

lemma closedCheck_eq : closedCheck = true := by decide

lemma simpleCheck_eq : simpleCheck = true := by decide

lemma allRoots_closed {i : Fin Tag.F4.rank} {v : Fin Tag.F4.rank → ℤ}
    (hv : v ∈ allRoots) : reflect .F4 i v ∈ allRoots := by
  have hall := List.all_eq_true.1 closedCheck_eq
  have h2 : (f4Indices.all fun i => memAllRoots (reflect .F4 i v)) = true := hall v hv
  have hi : i ∈ f4Indices := by
    fin_cases i <;> simp [f4Indices]
  exact memAllRoots_eq_true.1 (List.all_eq_true.1 h2 i hi)

lemma simple_mem_allRoots (i : Fin Tag.F4.rank) : Pi.single i 1 ∈ allRoots := by
  have hall := List.all_eq_true.1 simpleCheck_eq
  have hi : i ∈ f4Indices := by
    fin_cases i <;> simp [f4Indices]
  exact memAllRoots_eq_true.1 (hall i hi)

theorem isRoot_mem_allRoots {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    α ∈ allRoots := by
  induction hα with
  | basis j => exact simple_mem_allRoots j
  | reflect i hv ih => exact allRoots_closed (i := i) ih

theorem pos_or_neg_mem_f4PosRoots {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    α ∈ f4PosRoots ∨ -α ∈ f4PosRoots := by
  have h := isRoot_mem_allRoots hα
  simp only [allRoots, List.mem_append, List.mem_map] at h
  rcases h with h | ⟨β, hβ, hβeq⟩
  · exact Or.inl h
  · right
    rw [← hβeq, neg_neg]
    exact hβ

def goodNormalZ (w : Fin Tag.F4.rank → ℤ) : Bool :=
  (f4LongRootsP.any fun x => dot4Z w x.1 == 0) &&
    (f4ShortRootsP.any fun y => dot4Z w y.1 == 0)

def checkA (a : Fin Tag.F4.rank → ℤ) : Bool :=
  f4PosRoots.all fun b => f4PosRoots.all fun c => goodNormalZ (cofactorZ a b c)

private theorem checkA_0 : checkA (toF4 ![0,1,0,0]) = true := by decide
private theorem checkA_1 : checkA (toF4 ![0,1,2,0]) = true := by decide
private theorem checkA_2 : checkA (toF4 ![0,1,2,2]) = true := by decide
private theorem checkA_3 : checkA (toF4 ![1,0,0,0]) = true := by decide
private theorem checkA_4 : checkA (toF4 ![1,1,0,0]) = true := by decide
private theorem checkA_5 : checkA (toF4 ![1,1,2,0]) = true := by decide
private theorem checkA_6 : checkA (toF4 ![1,1,2,2]) = true := by decide
private theorem checkA_7 : checkA (toF4 ![1,2,2,0]) = true := by decide
private theorem checkA_8 : checkA (toF4 ![1,2,2,2]) = true := by decide
private theorem checkA_9 : checkA (toF4 ![1,2,4,2]) = true := by decide
private theorem checkA_10 : checkA (toF4 ![1,3,4,2]) = true := by decide
private theorem checkA_11 : checkA (toF4 ![2,3,4,2]) = true := by decide
private theorem checkA_12 : checkA (toF4 ![0,0,0,1]) = true := by decide
private theorem checkA_13 : checkA (toF4 ![0,0,1,0]) = true := by decide
private theorem checkA_14 : checkA (toF4 ![0,0,1,1]) = true := by decide
private theorem checkA_15 : checkA (toF4 ![0,1,1,0]) = true := by decide
private theorem checkA_16 : checkA (toF4 ![0,1,1,1]) = true := by decide
private theorem checkA_17 : checkA (toF4 ![0,1,2,1]) = true := by decide
private theorem checkA_18 : checkA (toF4 ![1,1,1,0]) = true := by decide
private theorem checkA_19 : checkA (toF4 ![1,1,1,1]) = true := by decide
private theorem checkA_20 : checkA (toF4 ![1,1,2,1]) = true := by decide
private theorem checkA_21 : checkA (toF4 ![1,2,2,1]) = true := by decide
private theorem checkA_22 : checkA (toF4 ![1,2,3,1]) = true := by decide
private theorem checkA_23 : checkA (toF4 ![1,2,3,2]) = true := by decide

theorem f4TripleCheck {a b c : Fin Tag.F4.rank → ℤ} (ha : a ∈ f4PosRoots)
    (hb : b ∈ f4PosRoots) (hc : c ∈ f4PosRoots) :
    goodNormalZ (cofactorZ a b c) = true := by
  have hall : ∀ a ∈ f4PosRoots, checkA a = true := by
    unfold f4PosRoots
    simp only [List.forall_mem_cons, List.not_mem_nil]
    exact ⟨checkA_0, checkA_1, checkA_2, checkA_3, checkA_4, checkA_5, checkA_6, checkA_7,
        checkA_8, checkA_9, checkA_10, checkA_11, checkA_12, checkA_13, checkA_14, checkA_15,
        checkA_16, checkA_17, checkA_18, checkA_19, checkA_20, checkA_21, checkA_22, checkA_23,
        by simp⟩
  have h := hall a ha
  simp only [checkA, List.all_eq_true] at h
  exact h b hb c hc

theorem goodNormalZ_spec {w : Fin Tag.F4.rank → ℤ} (h : goodNormalZ w = true) :
    (∃ x ∈ f4LongRootsP, dot4Z w x.1 = 0) ∧
      ∃ y ∈ f4ShortRootsP, dot4Z w y.1 = 0 := by
  simpa [goodNormalZ, List.any_eq_true] using h

end CFSG.LocalAnalysis.GLTheoremA.T173O
