module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.OuterInvolution
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S1

open Matrix

variable (F : Type) [Field F]

@[expose] def reflDiagMat (i : Fin 4) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal fun j => if j = i then (-1 : F) else 1

theorem reflDiagMat_mul_self (i : Fin 4) : reflDiagMat F i * reflDiagMat F i = 1 := by
  unfold reflDiagMat
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

@[expose] def reflDiag (i : Fin 4) : GL (Fin 4) F :=
  ⟨reflDiagMat F i, reflDiagMat F i, reflDiagMat_mul_self F i, reflDiagMat_mul_self F i⟩

theorem reflDiag_mul_self (i : Fin 4) : reflDiag F i * reflDiag F i = 1 :=
  Units.ext (reflDiagMat_mul_self F i)

theorem reflDiag_comm (i j : Fin 4) : reflDiag F i * reflDiag F j = reflDiag F j * reflDiag F i := by
  apply Units.ext
  change reflDiagMat F i * reflDiagMat F j = reflDiagMat F j * reflDiagMat F i
  unfold reflDiagMat
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem det_reflDiag (i : Fin 4) : ((reflDiag F i : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1 := by
  change (reflDiagMat F i).det = -1
  unfold reflDiagMat
  rw [det_diagonal]
  fin_cases i <;> simp

theorem reflDiag_prod : reflDiag F 0 * reflDiag F 1 * reflDiag F 2 * reflDiag F 3 = -1 := by
  apply Units.ext
  change reflDiagMat F 0 * reflDiagMat F 1 * reflDiagMat F 2 * reflDiagMat F 3 = -1
  unfold reflDiagMat
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem reflDiag_apply_self (i : Fin 4) :
    ((reflDiag F i : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i i = -1 := by
  change reflDiagMat F i i i = -1
  simp [reflDiagMat]

theorem reflDiag_apply_ne {i j : Fin 4} (h : j ≠ i) :
    ((reflDiag F i : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) j j = 1 := by
  change reflDiagMat F i j j = 1
  simp [reflDiagMat, h]

theorem reflDiag_injective (h2 : (2 : F) ≠ 0) : Function.Injective (reflDiag F) := by
  intro i j hij
  by_contra hne
  have h1 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) i i) hij
  simp only [reflDiag_apply_self, reflDiag_apply_ne F (i := j) (j := i) hne] at h1
  apply h2
  linear_combination (-1 : F) * h1

section Frame

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Generic Subgroup

@[expose] def ActsAsReflOn {C : Type*} [Group C] {K : Subgroup C} {F : Type} [Field F]
    {S : Subgroup (GL (Fin 4) F)} (e : ↥K ≃* ↥S) (c : C) (r : GL (Fin 4) F) : Prop :=
  ∀ k k' : ↥K, c * (k : C) * c⁻¹ = (k' : C) →
    ((e k' : ↥S) : GL (Fin 4) F) = r * ((e k : ↥S) : GL (Fin 4) F) * r⁻¹

variable {G : Type} [Group G]

@[expose] def S1FrameModel (x : G) (K : Subgroup (CentralizerBar x)) (u : Fin 4 → G)
    (hu : ∀ i, u i ∈ centralizer ({x} : Set G)) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : ↥K ≃* ↥(StatedSL 4 F)), Nat.card F % 4 = 3 ∧
      ∀ i : Fin 4, ActsAsReflOn e (barOf (hu i)) (reflDiag F i)) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (e : ↥K ≃* ↥(StatedSU 4 q F)),
      Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧ ∀ i : Fin 4, ActsAsReflOn e (barOf (hu i)) (reflDiag F i))

@[expose] def S1Frame (x : G) (K : Subgroup (CentralizerBar x)) (u : Fin 4 → G)
    (hu : ∀ i, u i ∈ centralizer ({x} : Set G)) : Prop :=
  (∀ i, IsConj x (u i) ∧ u i * u i = 1 ∧ barOf (hu i) ∉ K) ∧
    (∀ i j, u i * u j = u j * u i) ∧ u 0 * u 1 * u 2 * u 3 = x ∧ (∀ i j, i ≠ j → u i ≠ u j) ∧
    S1FrameModel x K u hu

end Frame

end CFSG.GH74.Generic.S1
