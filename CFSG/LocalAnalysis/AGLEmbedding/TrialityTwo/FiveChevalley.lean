module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveQuadratic

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Five

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def diagPoly (B : LinearMap.BilinForm K (σ → K)) : MvPolynomial σ K :=
  ∑ i, ∑ j, X i * (X j * C (B (Pi.single i 1) (Pi.single j 1)))

theorem eval_diagPoly (B : LinearMap.BilinForm K (σ → K)) (x : σ → K) :
    eval x (diagPoly B) = B x x := by
  conv_rhs => rw [← Matrix.toLinearMap₂'_toMatrix' (R := K) B, Matrix.toLinearMap₂'_apply]
  simp [diagPoly, smul_eq_mul]

theorem totalDegree_diagPoly_le (B : LinearMap.BilinForm K (σ → K)) :
    (diagPoly B).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun j _ => ?_
  calc (X i * (X j * C (B (Pi.single i 1) (Pi.single j 1)))).totalDegree
      ≤ (X i).totalDegree + (X j * C (B (Pi.single i 1) (Pi.single j 1))).totalDegree :=
        totalDegree_mul _ _
    _ ≤ (X i).totalDegree +
        ((X j).totalDegree + (C (B (Pi.single i 1) (Pi.single j 1))).totalDegree) := by
        gcongr
        exact totalDegree_mul _ _
    _ = 2 := by simp

theorem exists_mvPolynomial (Q : QuadraticForm K (σ → K)) :
    ∃ P : MvPolynomial σ K, P.totalDegree ≤ 2 ∧ ∀ x, eval x P = Q x := by
  refine ⟨diagPoly (Q.toBilin (Module.finBasis K (σ → K))), totalDegree_diagPoly_le _,
    fun x => ?_⟩
  rw [eval_diagPoly, ← LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.toQuadraticMap_toBilin]

theorem exists_ne_zero_common_zero [Finite K] (hK : Nat.card K = 2) (hσ : 6 < Fintype.card σ)
    (Q₁ Q₂ Q₃ : QuadraticForm K (σ → K)) :
    ∃ x : σ → K, x ≠ 0 ∧ Q₁ x = 0 ∧ Q₂ x = 0 ∧ Q₃ x = 0 := by
  classical
  have := Fintype.ofFinite K
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero hK)
  obtain ⟨P₁, hP₁, eP₁⟩ := exists_mvPolynomial Q₁
  obtain ⟨P₂, hP₂, eP₂⟩ := exists_mvPolynomial Q₂
  obtain ⟨P₃, hP₃, eP₃⟩ := exists_mvPolynomial Q₃
  let f : Fin 3 → MvPolynomial σ K := ![P₁, P₂, P₃]
  have hdeg : ∑ i, (f i).totalDegree < Fintype.card σ := by
    calc ∑ i, (f i).totalDegree ≤ ∑ _i : Fin 3, 2 := Finset.sum_le_sum fun i _ => by
          fin_cases i
          exacts [hP₁, hP₂, hP₃]
      _ = 6 := by simp
      _ < Fintype.card σ := hσ
  have hdvd : 2 ∣ Nat.card {x : σ → K // ∀ i, eval x (f i) = 0} := by
    simpa only [← Nat.card_eq_fintype_card] using char_dvd_card_solutions_of_fintype_sum_lt 2 hdeg
  have h0 : ∀ i, eval 0 (f i) = 0 := by
    intro i
    fin_cases i
    · exact (eP₁ 0).trans Q₁.map_zero
    · exact (eP₂ 0).trans Q₂.map_zero
    · exact (eP₃ 0).trans Q₃.map_zero
  let z : {x : σ → K // ∀ i, eval x (f i) = 0} := ⟨0, h0⟩
  have hpos : 0 < Nat.card {x : σ → K // ∀ i, eval x (f i) = 0} :=
    Nat.card_pos_iff.mpr ⟨⟨z⟩, inferInstance⟩
  have hgt : 1 < Nat.card {x : σ → K // ∀ i, eval x (f i) = 0} := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  have : Nontrivial {x : σ → K // ∀ i, eval x (f i) = 0} :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨y, hy⟩ := exists_ne z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_, ?_, ?_⟩
  · simpa [f, eP₁] using y.2 0
  · simpa [f, eP₂] using y.2 1
  · simpa [f, eP₃] using y.2 2

end CFSG.AGLEmbedding.TrialityTwo.Five
