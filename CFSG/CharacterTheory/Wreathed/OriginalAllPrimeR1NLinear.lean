module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersLayer

public section

namespace CFSG.Wreathed.OriginalAllPrime.R1NFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

variable {F : Type} [Field F]

theorem trace_eq_two_of_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP F p]
    {Z : SpecialLinearGroup (Fin 2) F} {k : ℕ} (hZ : Z ^ p ^ k = 1) : Z 0 0 + Z 1 1 = 2 := by
  have hM : (Z : Matrix (Fin 2) (Fin 2) F) ^ p ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hZ, Matrix.SpecialLinearGroup.coe_one]
  have h1 : ((Z : Matrix (Fin 2) (Fin 2) F) - 1) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right _), one_pow, hM, sub_self]
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent ⟨_, h1⟩).eq_zero
  rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_fin_two] at htr
  simp only [Fintype.card_fin, Nat.cast_ofNat] at htr
  linear_combination htr

theorem mul_self_of_trace_eq_zero {A : GL (Fin 2) F} (hA : A.val 0 0 + A.val 1 1 = 0) :
    A * A = GeneralLinearGroup.scalar (Fin 2) (-GeneralLinearGroup.det A) := by
  have hd : A.val 1 1 = -A.val 0 0 := by linear_combination hA
  apply Units.ext
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, GeneralLinearGroup.scalar,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hd] <;> ring

theorem matrixConjugation_matrixConjugation {A : GL (Fin 2) F}
    (hA : A.val 0 0 + A.val 1 1 = 0) (Z : SpecialLinearGroup (Fin 2) F) :
    matrixConjugation F A (matrixConjugation F A Z) = Z := by
  rw [← MulAut.mul_apply, ← map_mul, mul_self_of_trace_eq_zero hA, matrixConjugation_scalar,
    MulAut.one_apply]

theorem eq_one_of_commute_of_trace_eq_zero (h2 : (2 : F) ≠ 0) {A : GL (Fin 2) F}
    (hA : A.val 0 0 + A.val 1 1 = 0) {Z : SpecialLinearGroup (Fin 2) F}
    (htr : Z 0 0 + Z 1 1 = 2)
    (hc : SpecialLinearGroup.toGL Z * A = A * SpecialLinearGroup.toGL Z) : Z = 1 := by
  have hm := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F)) hc
  simp only [Units.val_mul] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  change Z 0 0 * A.val 0 0 + Z 0 1 * A.val 1 0 = A.val 0 0 * Z 0 0 + A.val 0 1 * Z 1 0 at e00
  change Z 0 0 * A.val 0 1 + Z 0 1 * A.val 1 1 = A.val 0 0 * Z 0 1 + A.val 0 1 * Z 1 1 at e01
  change Z 1 0 * A.val 0 0 + Z 1 1 * A.val 1 0 = A.val 1 0 * Z 0 0 + A.val 1 1 * Z 1 0 at e10
  have hdetZ : Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 = 1 := by
    have h := Z.2
    rw [det_fin_two] at h
    exact h
  have hdetA : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 ≠ 0 := by
    have h := GeneralLinearGroup.det_ne_zero A
    rwa [det_fin_two] at h
  set a := A.val 0 0
  set b := A.val 0 1
  set c := A.val 1 0
  set d := A.val 1 1
  have hd : d = -a := by linear_combination hA
  rw [hd] at e01 e10 hdetA
  set δ := Z 0 0 - Z 1 1 with hδ
  have hb : b * δ = 2 * a * Z 0 1 := by rw [hδ]; linear_combination e01
  have hc' : c * δ = 2 * a * Z 1 0 := by rw [hδ]; linear_combination -e10
  have hδsq : δ ^ 2 = -4 * (Z 0 1 * Z 1 0) := by
    rw [hδ]
    linear_combination (Z 0 0 + Z 1 1 + 2) * htr - 4 * hdetZ
  have hs : (a ^ 2 + b * c) * δ ^ 2 = 0 := by
    linear_combination a ^ 2 * hδsq + (c * δ) * hb + (2 * a * Z 0 1) * hc'
  have hs0 : a ^ 2 + b * c ≠ 0 := by
    intro h
    apply hdetA
    linear_combination -h
  have hδ0 : δ = 0 := by
    have := (mul_eq_zero.mp hs).resolve_left hs0
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hzz : Z 0 1 * Z 1 0 = 0 := by
    have h := hδsq
    rw [hδ0] at h
    have : -4 * (Z 0 1 * Z 1 0) = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr h4)
  have h01 : Z 0 1 = 0 ∧ Z 1 0 = 0 := by
    by_cases ha : a = 0
    · rw [ha] at hs0
      have hbc : b * c ≠ 0 := by simpa using hs0
      have hb0 : b ≠ 0 := left_ne_zero_of_mul hbc
      have hc0 : c ≠ 0 := right_ne_zero_of_mul hbc
      rw [ha] at e00
      have e00' : Z 0 1 * c = b * Z 1 0 := by linear_combination e00
      rcases mul_eq_zero.mp hzz with h | h
      · refine ⟨h, ?_⟩
        rw [h, zero_mul] at e00'
        exact (mul_eq_zero.mp e00'.symm).resolve_left hb0
      · refine ⟨?_, h⟩
        rw [h, mul_zero] at e00'
        exact (mul_eq_zero.mp e00').resolve_right hc0
    · have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
      rw [hδ0, mul_zero] at hb hc'
      exact ⟨(mul_eq_zero.mp hb.symm).resolve_left h2a,
        (mul_eq_zero.mp hc'.symm).resolve_left h2a⟩
  have h11 : Z 0 0 = 1 ∧ Z 1 1 = 1 := by
    have heq : Z 0 0 = Z 1 1 := by rw [hδ] at hδ0; linear_combination hδ0
    have h2z : 2 * Z 1 1 = 2 * 1 := by linear_combination htr - heq
    have hz : Z 1 1 = 1 := mul_left_cancel₀ h2 h2z
    exact ⟨heq.trans hz, hz⟩
  apply SL_ext_entries
  · rw [h11.1]; rfl
  · rw [h01.1]; rfl
  · rw [h01.2]; rfl
  · rw [h11.2]; rfl

theorem mul_mul_inv_eq_matrixConjugation (t Z : SpecialLinearGroup (Fin 2) F) :
    t * Z * t⁻¹ = matrixConjugation F (SpecialLinearGroup.toGL t) Z := by
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL, map_mul, map_mul, map_inv]

theorem eq_top_of_torus_le_of_rootSL_mem [Finite F] (h2 : (2 : F) ≠ 0) {i : F}
    (hi : i * i = -1) {K : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hT : Subgroup.centralizer {weyl F} ≤ K) (h1 : rootSL i hi 1 ∈ K)
    (h1' : rootSL (-i) (neg_mul_neg_eq_neg_one hi) 1 ∈ K) : K = ⊤ := by
  have key : ∀ (j : F) (hj : j * j = -1), rootSL j hj 1 ∈ K → ∀ l, rootSL j hj l ∈ K := by
    intro j hj hj1
    have hsq : ∀ μ : F, rootSL j hj (μ ^ 2) ∈ K := by
      intro μ
      by_cases hμ : μ = 0
      · rw [hμ, zero_pow two_ne_zero, rootSL_zero]
        exact K.one_mem
      obtain ⟨t, ht⟩ :=
        (CFSG.Wreathed.OddFieldTorus.torusToUnits_bijective h2 j hj).2 (Units.mk0 μ hμ)
      have hμt : (t : SpecialLinearGroup (Fin 2) F) 0 0 +
          j * (t : SpecialLinearGroup (Fin 2) F) 1 0 = μ := congrArg Units.val ht
      have htT : (t : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.centralizer {weyl F} := t.2
      have hmem : (t : SpecialLinearGroup (Fin 2) F) * rootSL j hj 1 *
          (t : SpecialLinearGroup (Fin 2) F)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (hT htT) hj1) (K.inv_mem (hT htT))
      rw [mul_mul_inv_eq_matrixConjugation,
        matrixConjugation_rootSL_of_commute hj (toGL_commute_weyl_of_mem htT)] at hmem
      have hsum := CFSG.Wreathed.OddFieldTorus.torus_sq_add_sq (L := F) htT
      have hD := sub_mul_ne_zero_of_commute_weyl hj (toGL_commute_weyl_of_mem htT)
      have hκ : ((SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 0 0 +
          (SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 1 0 * j) /
          ((SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 0 0 -
            (SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 2) F)).val 1 0 * j) =
              μ ^ 2 := by
        rw [div_eq_iff hD]
        change (t : SpecialLinearGroup (Fin 2) F) 0 0 +
            (t : SpecialLinearGroup (Fin 2) F) 1 0 * j =
          μ ^ 2 * ((t : SpecialLinearGroup (Fin 2) F) 0 0 -
            (t : SpecialLinearGroup (Fin 2) F) 1 0 * j)
        rw [← hμt]
        linear_combination
          -((t : SpecialLinearGroup (Fin 2) F) 0 0 +
              (t : SpecialLinearGroup (Fin 2) F) 1 0 * j) * hsum +
          ((t : SpecialLinearGroup (Fin 2) F) 0 0 + (t : SpecialLinearGroup (Fin 2) F) 1 0 * j) *
            (t : SpecialLinearGroup (Fin 2) F) 1 0 ^ 2 * hj
      rw [hκ, one_mul] at hmem
      exact hmem
    intro l
    obtain ⟨a, c, hac⟩ := CFSG.Wreathed.OddFieldTorus.exists_sq_add_sq h2 l
    rw [← hac, rootSL_add]
    exact K.mul_mem (hsq a) (hsq c)
  rw [eq_top_iff, ← closure_rootSL h2 hi, Subgroup.closure_le]
  rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
  · exact key i hi h1 l
  · exact key (-i) _ h1' l

end CFSG.Wreathed.OriginalAllPrime.R1NFacts
