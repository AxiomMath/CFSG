module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3FinInputs

public section

namespace CFSG.QuasithinUnique.A5

open Matrix

abbrev Mat4 := Matrix (Fin 4) (Fin 4) (ZMod 2)

local instance (priority := high) v4DecEq : DecidableEq V4 := fun x y =>
  decidable_of_iff (x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 ∧ x 3 = y 3) (by
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      funext i
      fin_cases i <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩)

@[expose] def Bf (x y : V4) : ZMod 2 := x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2

theorem quad_add : ∀ x y : V4, quadHyp (x + y) = quadHyp x + quadHyp y + Bf x y := by
  decide +kernel

theorem Bf_comm : ∀ x y : V4, Bf x y = Bf y x := by decide +kernel

theorem Bf_nondeg : ∀ x : V4, x ≠ 0 → ∃ y, Bf x y = 1 := by decide +kernel

theorem zmod2_add_self' : ∀ a : ZMod 2, a + a = 0 := by decide

theorem zmod2_neg : ∀ a : ZMod 2, -a = a := by decide

theorem V4_add_self (x : V4) : x + x = 0 := funext fun i => zmod2_add_self' (x i)

theorem V4_neg (x : V4) : -x = x := funext fun i => zmod2_neg (x i)

theorem V4_four (a b : V4) : a + b + a + b = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize a i = x
  generalize b i = y
  revert x y
  decide

theorem refl_involutive : ∀ x w : V4,
    (x + Bf x w • w) + Bf (x + Bf x w • w) w • w = x := by decide +kernel

@[expose] def matEq (A B : Mat4) : Bool :=
  decide (A 0 0 = B 0 0) && decide (A 0 1 = B 0 1) && decide (A 0 2 = B 0 2) &&
  decide (A 0 3 = B 0 3) && decide (A 1 0 = B 1 0) && decide (A 1 1 = B 1 1) &&
  decide (A 1 2 = B 1 2) && decide (A 1 3 = B 1 3) && decide (A 2 0 = B 2 0) &&
  decide (A 2 1 = B 2 1) && decide (A 2 2 = B 2 2) && decide (A 2 3 = B 2 3) &&
  decide (A 3 0 = B 3 0) && decide (A 3 1 = B 3 1) && decide (A 3 2 = B 3 2) &&
  decide (A 3 3 = B 3 3)

@[expose] def mm (A B : Mat4) : Mat4 :=
  Matrix.of fun i k => A i 0 * B 0 k + A i 1 * B 1 k + A i 2 * B 2 k + A i 3 * B 3 k

@[expose] def mv (A : Mat4) (x : V4) : V4 := fun i =>
  A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2 + A i 3 * x 3

@[expose] def vEq (x y : V4) : Bool :=
  decide (x 0 = y 0) && decide (x 1 = y 1) && decide (x 2 = y 2) && decide (x 3 = y 3)

theorem matEq_iff {A B : Mat4} : matEq A B = true ↔ A = B := by
  unfold matEq
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  · rintro rfl
    simp

theorem mm_eq (A B : Mat4) : mm A B = A * B := by
  ext i k
  simp [mm, Matrix.mul_apply, Fin.sum_univ_four]

theorem mv_eq (A : Mat4) (x : V4) : mv A x = A.mulVec x := by
  funext i
  simp [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem vEq_iff {x y : V4} : vEq x y = true ↔ x = y := by
  unfold vEq
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    simp

@[expose] def memL (A : Mat4) (l : List Mat4) : Bool := l.any fun B => matEq A B

theorem memL_iff {A : Mat4} {l : List Mat4} : memL A l = true ↔ A ∈ l := by
  unfold memL
  simp [List.any_eq_true, matEq_iff]

@[expose] def cube1 (A : Mat4) : Bool := matEq (mm A (mm A A)) 1

@[expose] def pow9 (A : Mat4) : Bool :=
  matEq (mm (mm A (mm A A)) (mm (mm A (mm A A)) (mm A (mm A A)))) 1

@[expose] def sq1 (A : Mat4) : Bool := matEq (mm A A) 1

theorem cube1_iff {A : Mat4} : cube1 A = true ↔ A ^ 3 = 1 := by
  rw [cube1, matEq_iff, mm_eq, mm_eq, ← pow_three]

theorem pow9_iff {A : Mat4} : pow9 A = true ↔ A ^ 9 = 1 := by
  rw [pow9, matEq_iff]
  simp only [mm_eq]
  rw [← pow_three, ← pow_three, ← pow_mul]

theorem sq1_iff {A : Mat4} : sq1 A = true ↔ A * A = 1 := by
  rw [sq1, matEq_iff, mm_eq]

@[expose] def O4List : List Mat4 :=
  [!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
   !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
   !![0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
   !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1],
   !![0, 0, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0],
   !![0, 1, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 0],
   !![0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 1],
   !![0, 1, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 1, 1, 1],
   !![0, 1, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 1, 1, 1],
   !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0],
   !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
   !![0, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0],
   !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0],
   !![0, 1, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0],
   !![0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0],
   !![0, 1, 0, 1; 0, 1, 1, 0; 1, 1, 1, 1; 0, 1, 0, 0],
   !![0, 1, 1, 0; 0, 1, 0, 1; 1, 1, 1, 1; 0, 1, 0, 0],
   !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
   !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
   !![0, 1, 0, 0; 1, 0, 0, 1; 0, 0, 0, 1; 0, 1, 1, 0],
   !![0, 1, 0, 0; 1, 0, 1, 0; 0, 0, 1, 0; 0, 1, 0, 1],
   !![0, 1, 0, 0; 1, 0, 0, 1; 0, 1, 1, 0; 0, 0, 0, 1],
   !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0],
   !![0, 1, 0, 0; 1, 1, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0],
   !![0, 1, 0, 0; 1, 1, 1, 1; 0, 1, 1, 0; 0, 1, 0, 1],
   !![0, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0],
   !![0, 0, 1, 0; 1, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, 0],
   !![0, 0, 0, 1; 1, 1, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1],
   !![0, 0, 1, 0; 1, 1, 1, 1; 0, 1, 1, 0; 1, 0, 1, 0],
   !![0, 1, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0],
   !![0, 1, 1, 0; 1, 0, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1],
   !![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 1],
   !![0, 1, 1, 0; 1, 0, 1, 0; 0, 0, 1, 0; 1, 1, 1, 1],
   !![0, 0, 0, 1; 1, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1],
   !![0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0],
   !![0, 0, 0, 1; 1, 1, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1],
   !![0, 0, 1, 0; 1, 1, 1, 1; 1, 0, 1, 0; 0, 1, 1, 0],
   !![0, 1, 0, 1; 1, 0, 0, 0; 1, 0, 1, 0; 0, 0, 0, 1],
   !![0, 1, 1, 0; 1, 0, 0, 0; 1, 0, 0, 1; 0, 0, 1, 0],
   !![0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1; 0, 0, 0, 1],
   !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 1, 1; 0, 0, 1, 0],
   !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
   !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 1, 1, 0],
   !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1],
   !![1, 0, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1],
   !![1, 0, 1, 0; 0, 1, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0],
   !![1, 1, 1, 1; 0, 1, 0, 0; 0, 1, 0, 1; 0, 1, 1, 0],
   !![1, 1, 1, 1; 0, 1, 0, 0; 0, 1, 1, 0; 0, 1, 0, 1],
   !![1, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 0],
   !![1, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 1; 1, 0, 0, 0],
   !![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 0, 1; 1, 0, 1, 0],
   !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 1],
   !![1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 0, 1; 1, 1, 1, 1],
   !![1, 0, 1, 0; 0, 1, 1, 0; 0, 0, 1, 0; 1, 1, 1, 1],
   !![1, 1, 1, 1; 0, 0, 0, 1; 0, 1, 0, 1; 1, 0, 0, 1],
   !![1, 1, 1, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 1, 0],
   !![1, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 1, 0],
   !![1, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 1],
   !![1, 0, 0, 0; 0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 0, 1],
   !![1, 0, 0, 0; 0, 1, 1, 0; 1, 0, 0, 1; 0, 0, 1, 0],
   !![1, 0, 0, 1; 0, 1, 0, 1; 1, 1, 1, 1; 0, 0, 0, 1],
   !![1, 0, 1, 0; 0, 1, 1, 0; 1, 1, 1, 1; 0, 0, 1, 0],
   !![1, 1, 1, 1; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1],
   !![1, 1, 1, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 1, 0],
   !![1, 0, 0, 1; 1, 0, 1, 0; 1, 0, 0, 0; 1, 1, 1, 1],
   !![1, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 1, 1, 1, 1],
   !![1, 0, 0, 1; 1, 0, 1, 0; 1, 1, 1, 1; 1, 0, 0, 0],
   !![1, 0, 1, 0; 1, 0, 0, 1; 1, 1, 1, 1; 1, 0, 0, 0],
   !![1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 1, 0],
   !![1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0; 1, 0, 0, 1],
   !![1, 1, 1, 1; 1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0],
   !![1, 1, 1, 1; 1, 0, 0, 0; 1, 0, 1, 0; 1, 0, 0, 1]]

@[expose] def E3List : List Mat4 :=
  [!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
   !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1],
   !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0],
   !![0, 1, 0, 0; 1, 1, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0],
   !![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 1],
   !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 1, 1; 0, 0, 1, 0],
   !![1, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 0],
   !![1, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 1],
   !![1, 1, 1, 1; 1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0]]

@[expose] def colsOf (c : O4Cols) : Fin 4 → V4 := ![c.1.1, c.2.1.1, c.2.2.1.1, c.2.2.2.1]

@[expose] def matOfCols (c : O4Cols) : Mat4 := Matrix.of fun i j => colsOf c j i

theorem memL_matOfCols : ∀ c : O4Cols, memL (matOfCols c) O4List = true := by decide +kernel

theorem exists_cols {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) :
    ∃ c : O4Cols, matOfCols c = (g : Mat4) := by
  have hq : ∀ v : V4, quadHyp ((g : Mat4).mulVec v) = quadHyp v := hg
  let col : Fin 4 → V4 := fun i => (g : Mat4).mulVec (Pi.single i 1)
  have hsum : ∀ i j, quadHyp (col i + col j) =
      quadHyp ((Pi.single i 1 : V4) + Pi.single j 1) := by
    intro i j
    have : col i + col j = (g : Mat4).mulVec ((Pi.single i 1 : V4) + Pi.single j 1) := by
      simp only [col, Matrix.mulVec_add]
    rw [this]
    exact hq _
  have hone : ∀ i, quadHyp (col i) = quadHyp (Pi.single i 1 : V4) := fun i => hq _
  refine ⟨⟨⟨col 0, (hone 0).trans (by decide +kernel)⟩,
    ⟨⟨col 1, (hone 1).trans (by decide +kernel), (hsum 0 1).trans (by decide +kernel)⟩,
    ⟨⟨col 2, (hone 2).trans (by decide +kernel), (hsum 0 2).trans (by decide +kernel),
      (hsum 1 2).trans (by decide +kernel)⟩,
    ⟨col 3, (hone 3).trans (by decide +kernel), (hsum 0 3).trans (by decide +kernel),
      (hsum 1 3).trans (by decide +kernel), (hsum 2 3).trans (by decide +kernel)⟩⟩⟩⟩, ?_⟩
  ext i j
  fin_cases j <;> simp [matOfCols, colsOf, col]

theorem mem_O4List {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) : (g : Mat4) ∈ O4List := by
  obtain ⟨c, hc⟩ := exists_cols hg
  rw [← hc]
  exact memL_iff.mp (memL_matOfCols c)

theorem gl_cube_iff (g : GL (Fin 4) (ZMod 2)) : g ^ 3 = 1 ↔ cube1 (g : Mat4) = true := by
  rw [cube1_iff, ← Units.val_pow_eq_pow_val]
  exact ⟨fun h => by rw [h]; rfl, fun h => Units.ext h⟩

theorem gl_pow9_iff (g : GL (Fin 4) (ZMod 2)) : g ^ 9 = 1 ↔ pow9 (g : Mat4) = true := by
  rw [pow9_iff, ← Units.val_pow_eq_pow_val]
  exact ⟨fun h => by rw [h]; rfl, fun h => Units.ext h⟩

theorem gl_sq1_iff (g : GL (Fin 4) (ZMod 2)) : g * g = 1 ↔ sq1 (g : Mat4) = true := by
  rw [sq1_iff, ← Units.val_mul]
  exact ⟨fun h => by rw [h]; rfl, fun h => Units.ext h⟩

@[expose] def VSL : List Mat4 := [1, Mt1, Ms01, mm Mt1 Ms01]

@[expose] def ns6 : List V4 :=
  [![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0]]

@[expose] def allV : List V4 :=
  [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 1, 0, 1],
   ![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
   ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]]

@[expose] def reflV (w x : V4) : V4 := fun i => x i + Bf x w * w i

theorem ns6_q : ∀ w ∈ ns6, quadHyp w = 1 := by decide +kernel

theorem allV_mem : ∀ x : V4, x ∈ allV := by decide +kernel

theorem reflV_eq (w x : V4) : reflV w x = x + Bf x w • w := by
  funext i
  simp [reflV]

theorem E3_allb : O4List.all (fun A => !cube1 A || memL A E3List) = true := by decide +kernel

theorem F1b : E3List.all (fun A => E3List.all (fun B => cube1 (mm A B))) = true := by
  decide +kernel

theorem F2b : O4List.all (fun A => !pow9 A || cube1 A) = true := by decide +kernel

theorem F3b : O4List.all (fun A => !sq1 A || VSL.any (fun V => cube1 (mm A V)) ||
    ns6.any (fun w => allV.all (fun x => vEq (mv A x) (reflV w x)))) = true := by
  decide +kernel

theorem F4b : O4List.all (fun A =>
    !(VSL.all (fun V => VSL.any (fun V' => matEq (mm A V) (mm V' A)))) || memL A VSL ||
    VSL.any (fun V => ns6.any (fun w => allV.all (fun x =>
      vEq (mv (mm A V) x) (reflV w x))))) = true := by decide +kernel

theorem E3_all : ∀ A ∈ O4List, cube1 A = true → memL A E3List = true := by
  intro A hA h
  have := List.all_eq_true.mp E3_allb A hA
  simpa [h] using this

theorem F1 : ∀ A ∈ E3List, ∀ B ∈ E3List, cube1 (mm A B) = true := by
  intro A hA B hB
  exact List.all_eq_true.mp (List.all_eq_true.mp F1b A hA) B hB

theorem F2 : ∀ A ∈ O4List, pow9 A = true → cube1 A = true := by
  intro A hA h
  have := List.all_eq_true.mp F2b A hA
  simpa [h] using this

theorem F3 : ∀ A ∈ O4List, sq1 A = true →
    (∃ V ∈ VSL, cube1 (mm A V) = true) ∨
      ∃ w ∈ ns6, ∀ x ∈ allV, vEq (mv A x) (reflV w x) = true := by
  intro A hA h
  have := List.all_eq_true.mp F3b A hA
  simpa [h, List.any_eq_true, List.all_eq_true] using this

theorem F4 : ∀ A ∈ O4List,
    (∀ V ∈ VSL, ∃ V' ∈ VSL, matEq (mm A V) (mm V' A) = true) → memL A VSL = false →
    ∃ V ∈ VSL, ∃ w ∈ ns6, ∀ x ∈ allV, vEq (mv (mm A V) x) (reflV w x) = true := by
  intro A hA h1 h2
  have := List.all_eq_true.mp F4b A hA
  have hall : VSL.all (fun V => VSL.any (fun V' => matEq (mm A V) (mm V' A))) = true := by
    simp only [List.all_eq_true, List.any_eq_true]
    exact h1
  rw [hall, h2] at this
  simpa [List.any_eq_true, List.all_eq_true] using this

theorem Esub_mul {g h : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) (hh : h ∈ O4PlusTwo)
    (h1 : g ^ 3 = 1) (h2 : h ^ 3 = 1) : (g * h) ^ 3 = 1 := by
  rw [gl_cube_iff] at h1 h2 ⊢
  rw [Units.val_mul, ← mm_eq]
  exact F1 _ (memL_iff.mp (E3_all _ (mem_O4List hg) h1)) _
    (memL_iff.mp (E3_all _ (mem_O4List hh) h2))

theorem odd_cube {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) (h9 : g ^ 9 = 1) : g ^ 3 = 1 := by
  rw [gl_pow9_iff] at h9
  rw [gl_cube_iff]
  exact F2 _ (mem_O4List hg) h9

theorem mem_VSL {V : Mat4} : V ∈ VSL ↔ V = 1 ∨ V = Mt1 ∨ V = Ms01 ∨ V = Mt1 * Ms01 := by
  simp [VSL, mm_eq]

theorem mulVec_eq_refl {A : Mat4} {w : V4}
    (h : ∀ x ∈ allV, vEq (mv A x) (reflV w x) = true) :
    ∀ x : V4, A.mulVec x = x + Bf x w • w := by
  intro x
  have := vEq_iff.mp (h x (allV_mem x))
  rw [mv_eq, reflV_eq] at this
  exact this

theorem invol_cases {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) (h2 : g * g = 1) :
    (∃ V ∈ VSL, ((g : Mat4) * V) ^ 3 = 1) ∨
      ∃ w : V4, quadHyp w = 1 ∧ ∀ x : V4, (g : Mat4).mulVec x = x + Bf x w • w := by
  rcases F3 _ (mem_O4List hg) ((gl_sq1_iff g).mp h2) with ⟨V, hV, hc⟩ | ⟨w, hw, hx⟩
  · left
    refine ⟨V, hV, ?_⟩
    rw [← mm_eq]
    exact cube1_iff.mp hc
  · exact Or.inr ⟨w, ns6_q w hw, mulVec_eq_refl hx⟩

theorem normS_cases {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo)
    (hn : ∀ V ∈ VSL, ∃ V' ∈ VSL, (g : Mat4) * V = V' * (g : Mat4)) (hnot : (g : Mat4) ∉ VSL) :
    ∃ V ∈ VSL, ∃ w : V4, quadHyp w = 1 ∧
      ∀ x : V4, ((g : Mat4) * V).mulVec x = x + Bf x w • w := by
  have hn' : ∀ V ∈ VSL, ∃ V' ∈ VSL, matEq (mm (g : Mat4) V) (mm V' (g : Mat4)) = true := by
    intro V hV
    obtain ⟨V', hV', h⟩ := hn V hV
    exact ⟨V', hV', matEq_iff.mpr (by rw [mm_eq, mm_eq]; exact h)⟩
  have hnot' : memL (g : Mat4) VSL = false := by
    cases h : memL (g : Mat4) VSL
    · rfl
    · exact absurd (memL_iff.mp h) hnot
  obtain ⟨V, hV, w, hw, hx⟩ := F4 _ (mem_O4List hg) hn' hnot'
  refine ⟨V, hV, w, ns6_q w hw, ?_⟩
  have := mulVec_eq_refl hx
  intro x
  rw [← mm_eq]
  exact this x

theorem mat4_ext {A B : Mat4} (h : ∀ x : V4, A.mulVec x = B.mulVec x) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

@[expose] def inPl (w a : V4) : Prop := a = 0 ∨ (quadHyp a = 1 ∧ Bf a w = 0 ∧ a ≠ w)

@[expose] def inPl' (w x : V4) : Prop := x = 0 ∨ (quadHyp x = 1 ∧ ¬ inPl w x)

instance (w a : V4) : Decidable (inPl w a) := by unfold inPl; infer_instance

instance (w x : V4) : Decidable (inPl' w x) := by unfold inPl'; infer_instance

theorem pl_add : ∀ w a b : V4, quadHyp w = 1 → inPl w a → inPl w b → inPl w (a + b) := by
  decide +kernel

theorem pl_q : ∀ w a : V4, inPl w a → a ≠ 0 → quadHyp a = 1 := by decide +kernel

theorem pl_Bf : ∀ w a : V4, inPl w a → Bf a w = 0 := by decide +kernel

theorem pl'_add : ∀ w x y : V4, quadHyp w = 1 → inPl' w x → inPl' w y → inPl' w (x + y) := by
  decide +kernel

theorem pl'_w : ∀ w : V4, quadHyp w = 1 → inPl' w w := by decide +kernel

theorem pl_orth : ∀ w a x : V4, quadHyp w = 1 → inPl w a → inPl' w x → Bf a x = 0 := by
  decide +kernel

theorem pl_perp : ∀ w x : V4, quadHyp w = 1 → (∀ a, inPl w a → Bf a x = 0) → inPl' w x := by
  decide +kernel

theorem pl_perp' : ∀ w a : V4, quadHyp w = 1 → (∀ x, inPl' w x → Bf a x = 0) → inPl w a := by
  decide +kernel

theorem pl_inf : ∀ w a : V4, quadHyp w = 1 → inPl w a → inPl' w a → a = 0 := by decide +kernel

theorem pl_Bf1 : ∀ w a b : V4, quadHyp w = 1 → inPl w a → inPl w b → a ≠ 0 → b ≠ 0 → a ≠ b →
    Bf a b = 1 := by decide +kernel

theorem pl'_refl : ∀ w x : V4, quadHyp w = 1 → inPl' w x → inPl' w (x + Bf x w • w) := by
  decide +kernel

theorem pl'_fix : ∀ w x : V4, quadHyp w = 1 → inPl' w x → Bf x w = 0 → x = 0 ∨ x = w := by
  decide +kernel

theorem pl'_Bfw : ∀ w x : V4, quadHyp w = 1 → inPl' w x → x ≠ 0 → x ≠ w → Bf x w = 1 := by
  decide +kernel

theorem pl'_other : ∀ w : V4, quadHyp w = 1 → ∃ w', inPl' w w' ∧ w' ≠ 0 ∧ w' ≠ w := by
  decide +kernel

theorem pl_split : ∀ w a : V4, quadHyp w = 1 → inPl w a → a ≠ 0 →
    ∃ x : V4, x ≠ x + a ∧ x ≠ 0 ∧ x + a ≠ 0 ∧ quadHyp x = 0 ∧ quadHyp (x + a) = 0 ∧
      Bf x w = 0 ∧ Bf (x + a) w = 0 := by decide +kernel

theorem pl_basis : ∀ w : V4, quadHyp w = 1 → ∃ a1 a2 : V4, inPl w a1 ∧ inPl w a2 ∧ a1 ≠ 0 ∧
    a2 ≠ 0 ∧ a1 ≠ a2 ∧ (∀ x, inPl w x → x = 0 ∨ x = a1 ∨ x = a2 ∨ x = a1 + a2) ∧
    ∀ c1 c2 : ZMod 2, ∃ a, inPl w a ∧ Bf a a1 = c1 ∧ Bf a a2 = c2 := by decide +kernel

@[expose] def cA : Mat4 := !![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 1]

@[expose] def cB : Mat4 := !![0, 1, 0, 0; 1, 1, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0]

@[expose] def CProp (c : Mat4) (w : V4) : Prop :=
  (∀ x, inPl' w x → mv c x = x) ∧ (∀ a, inPl w a → inPl w (mv c a)) ∧
    (∀ a, inPl w a → ∃ b, inPl w b ∧ b + mv c b = a) ∧ (∀ x, Bf (mv c x) w = Bf x w)

instance (c : Mat4) (w : V4) : Decidable (CProp c w) := by unfold CProp; infer_instance

theorem CProp_cases : ∀ w : V4, quadHyp w = 1 → CProp cA w ∨ CProp cB w := by decide +kernel

theorem cA_cube : cA * (cA * cA) = 1 := by
  rw [← mm_eq, ← mm_eq]
  exact matEq_iff.mp (by decide +kernel)

theorem cB_cube : cB * (cB * cB) = 1 := by
  rw [← mm_eq, ← mm_eq]
  exact matEq_iff.mp (by decide +kernel)

theorem cA_quad : ∀ v : V4, quadHyp (cA.mulVec v) = quadHyp v := by
  intro v
  rw [← mv_eq]
  revert v
  decide +kernel

theorem cB_quad : ∀ v : V4, quadHyp (cB.mulVec v) = quadHyp v := by
  intro v
  rw [← mv_eq]
  revert v
  decide +kernel

theorem cA_ne : cA ≠ 1 := by
  intro h
  have := matEq_iff.mpr h
  revert this
  decide +kernel

theorem cB_ne : cB ≠ 1 := by
  intro h
  have := matEq_iff.mpr h
  revert this
  decide +kernel

@[expose] def cAU : GL (Fin 4) (ZMod 2) :=
  ⟨cA, cA * cA, cA_cube, (mul_assoc cA cA cA).trans cA_cube⟩

@[expose] def cBU : GL (Fin 4) (ZMod 2) :=
  ⟨cB, cB * cB, cB_cube, (mul_assoc cB cB cB).trans cB_cube⟩

theorem cAU_mem : cAU ∈ O4PlusTwo := fun v => cA_quad v

theorem cBU_mem : cBU ∈ O4PlusTwo := fun v => cB_quad v

theorem cAU_cube : cAU ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; show cA ^ 3 = 1; rw [pow_three]; exact cA_cube)

theorem cBU_cube : cBU ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; show cB ^ 3 = 1; rw [pow_three]; exact cB_cube)

theorem cAU_ne : cAU ≠ 1 := fun h => cA_ne (congrArg Units.val h)

theorem cBU_ne : cBU ≠ 1 := fun h => cB_ne (congrArg Units.val h)

theorem exists_c {w : V4} (hw : quadHyp w = 1) : ∃ c : GL (Fin 4) (ZMod 2), c ∈ O4PlusTwo ∧
    c ^ 3 = 1 ∧ c ≠ 1 ∧ (∀ x, inPl' w x → (c : Mat4).mulVec x = x) ∧
    (∀ a, inPl w a → inPl w ((c : Mat4).mulVec a)) ∧
    (∀ a, inPl w a → ∃ b, inPl w b ∧ b + (c : Mat4).mulVec b = a) ∧
    (∀ x, Bf ((c : Mat4).mulVec x) w = Bf x w) := by
  rcases CProp_cases w hw with h | h
  · refine ⟨cAU, cAU_mem, cAU_cube, cAU_ne, ?_⟩
    have e : (cAU : Mat4) = cA := rfl
    rw [e]
    simpa only [CProp, mv_eq] using h
  · refine ⟨cBU, cBU_mem, cBU_cube, cBU_ne, ?_⟩
    have e : (cBU : Mat4) = cB := rfl
    rw [e]
    simpa only [CProp, mv_eq] using h

theorem refl_sq {g : Mat4} {w : V4} (hg : ∀ x : V4, g.mulVec x = x + Bf x w • w) : g * g = 1 := by
  apply mat4_ext
  intro x
  rw [← Matrix.mulVec_mulVec, hg x, hg (x + Bf x w • w), refl_involutive, Matrix.one_mulVec]

theorem comm_refl {c g : Mat4} {w : V4} (hg : ∀ x : V4, g.mulVec x = x + Bf x w • w)
    (hcw : c.mulVec w = w) (hB : ∀ x, Bf (c.mulVec x) w = Bf x w) : c * g = g * c := by
  apply mat4_ext
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg x, hg (c.mulVec x), Matrix.mulVec_add,
    Matrix.mulVec_smul, hcw, hB]

end CFSG.QuasithinUnique.A5
