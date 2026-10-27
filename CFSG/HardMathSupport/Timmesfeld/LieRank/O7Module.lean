module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Elts
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank.O7

open Matrix CFSG.AGLEmbedding

@[expose] def actMat : Fin 7 → Matrix (Fin 5) (Fin 5) K :=
  ![!![1, 0, 0, 2, 0;
     0, 1, 1, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1],
   !![1, 2, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 1, 1, 0;
     0, 0, 0, 0, 1],
   !![1, 0, 2, 0, 1;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 1, 0, 1],
   !![1, 0, 0, 0, 0;
     0, 1, 0, 2, 1;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 1, 1],
   !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 2, 0, 1, 2;
     0, 2, 0, 0, 1],
   !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     2, 0, 1, 0, 2;
     0, 0, 0, 1, 0;
     2, 0, 0, 0, 1],
   !![1, 0, 2, 2, 2;
     0, 1, 0, 2, 1;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 2, 1, 1]]

@[expose] def actEl : Fin 7 → Om7 := ![qE 0, qE 1, qE 2, qE 3, gE 0, gE 1, gE 2]

theorem aE_comm : ∀ i j : Fin 5, aE i * aE j = aE j * aE i := by decide +kernel

theorem aE_pow : ∀ i : Fin 5, aE i ^ 3 = 1 := by decide +kernel

theorem aE_indep : ∀ c : Fin 5 → ZMod 3,
    ((List.finRange 5).map fun k => aE k ^ (c k).val).prod = 1 → c = 0 := by
  decide +kernel

theorem actEl_act : ∀ (j : Fin 7) (i : Fin 5), actEl j * aE i * (actEl j)⁻¹ =
    ((List.finRange 5).map fun k => aE k ^ (actMat j k i).val).prod := by
  decide +kernel

@[expose] def modSpec : ModuleSpec Om7 3 where
  n := 5
  m := 7
  a := aE
  g := actEl
  M := actMat
  comm := aE_comm
  pow := aE_pow
  indep := aE_indep
  act := actEl_act

theorem noFun_O7 : modSpec.NoFun := by
  intro v hv
  have : ∀ w : Fin 5 → K, (∀ j : Fin 7, w ᵥ* actMat j = w) → w = 0 := by decide +kernel
  exact this v hv

@[expose] def altE : Fin 10 → Matrix (Fin 5) (Fin 5) K :=
  ![!![0, 1, 0, 0, 0; 2, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 1, 0, 0; 0, 0, 0, 0, 0; 2, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 0, 1, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 2, 0, 0, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 2, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 2, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 0; 0, 2, 0, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 2, 0, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 2, 0, 0; 0, 0, 0, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 2, 0, 0],
   !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 2, 0]]

@[expose] def altIdx : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

@[expose] def pivRow : Fin 10 → Fin 7 × Fin 5 × Fin 5 :=
  ![(0, 0, 2), (0, 2, 3), (0, 2, 4), (0, 3, 4), (1, 0, 2), (1, 1, 2), (1, 2, 4), (3, 2, 3),
    (3, 2, 4), (4, 1, 2)]

@[expose] def Cpiv : Matrix (Fin 10) (Fin 10) K :=
  Matrix.of fun p k => ((actMat (pivRow p).1)ᵀ * altE k * actMat (pivRow p).1 - altE k)
    (pivRow p).2.1 (pivRow p).2.2

@[expose] def CpivInv : Matrix (Fin 10) (Fin 10) K :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0;
    1, 2, 0, 0, 2, 2, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 2, 2, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

theorem CpivInv_mul : CpivInv * Cpiv = 1 := by decide +kernel

theorem alt_eq_sum {B : Matrix (Fin 5) (Fin 5) K} (hB : Bᵀ = -B) :
    B = ∑ k, B (altIdx k).1 (altIdx k).2 • altE k := by
  have h : ∀ a c : Fin 5, c < a → B a c = - B c a := fun a c _ => by
    have := congrFun (congrFun hB c) a
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using this
  have h0 : ∀ a, B a a = 0 := fun a => by
    have := congrFun (congrFun hB a) a
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    revert this
    generalize B a a = x
    revert x
    decide
  have hn : ∀ x : K, -x = x * 2 := by decide
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [altE, altIdx, Fin.sum_univ_succ, h0, h, hn]

theorem noAlt_aux (B : Matrix (Fin 5) (Fin 5) K) (hB : Bᵀ = -B)
    (hinv : ∀ j, (actMat j)ᵀ * B * actMat j = B) : B = 0 := by
  set b : Fin 10 → K := fun k => B (altIdx k).1 (altIdx k).2 with hb
  have hsum := alt_eq_sum hB
  have hrow : ∀ p, ∑ k, Cpiv p k * b k = 0 := by
    intro p
    have h1 := congrFun (congrFun (hinv (pivRow p).1) (pivRow p).2.1) (pivRow p).2.2
    rw [hsum] at h1
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at h1
    simp only [Cpiv, Matrix.of_apply, Matrix.sub_apply, sub_mul]
    refine Eq.trans (Finset.sum_sub_distrib _ _) (sub_eq_zero.2 ?_)
    calc _ = ∑ k, b k * ((actMat (pivRow p).1)ᵀ * altE k * actMat (pivRow p).1)
          (pivRow p).2.1 (pivRow p).2.2 := Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = _ := h1
      _ = _ := Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hb0 : b = 0 := by
    have h2 : Cpiv *ᵥ b = 0 := funext fun p => by simpa [Matrix.mulVec, dotProduct] using hrow p
    calc b = (CpivInv * Cpiv) *ᵥ b := by rw [CpivInv_mul, Matrix.one_mulVec]
      _ = CpivInv *ᵥ (Cpiv *ᵥ b) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h2, Matrix.mulVec_zero]
  have hk : ∀ k, B (altIdx k).1 (altIdx k).2 = 0 := fun k => congrFun hb0 k
  exact hsum.trans (Finset.sum_eq_zero fun k _ => by rw [hk k, zero_smul])

theorem noAlt_O7 : modSpec.NoAlt := fun B hB hinv => noAlt_aux B hB hinv

end CFSG.HardMathSupport.Timmesfeld.LieRank.O7
