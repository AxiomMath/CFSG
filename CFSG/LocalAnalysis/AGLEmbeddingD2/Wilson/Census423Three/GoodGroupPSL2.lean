module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroupGen
public import CFSG.Quasithin.Background.C126NatSL2

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

@[expose] def sl2Three (K : Type) [Field K] : SL(2, K) :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

omit [Finite K] in
theorem sl2Three_pow_three : sl2Three K ^ 3 = 1 := by
  have h : sl2Three K ^ 3 = sl2Three K * sl2Three K * sl2Three K := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  rw [h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Three, Matrix.mul_apply, Fin.sum_univ_two]

omit [Finite K] in
theorem sl2Three_ne_one : sl2Three K ≠ 1 := by
  intro h
  have := congrArg (fun m : SL(2, K) => (m : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [sl2Three] at this

omit [Finite K] in
theorem sl2Three_not_mem_center :
    sl2Three K ∉ Subgroup.center SL(2, K) := by
  intro hc
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hc with h | h
  · exact sl2Three_ne_one h
  · have := congrArg (fun m : SL(2, K) => (m : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [sl2Three] at this

theorem GoodGroup.psl2 (h3 : ringChar K ≠ 3) (h5 : 5 ≤ Nat.card K)
    (hσ : ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ = 1) : GoodGroup (PSL2 K) where
  rad N hN hs n hn y :=
    rad_of_isQuasisimple (isQuasisimple_psl2_of_four_le_card (by omega)) hN hs n hn y
  elt3 := by
    refine ⟨QuotientGroup.mk (sl2Three K), ?_, ?_⟩
    · intro h
      exact sl2Three_not_mem_center ((QuotientGroup.eq_one_iff _).mp h)
    · rw [← QuotientGroup.mk_pow, sl2Three_pow_three]
      rfl
  noCentral3 z hz _ := by
    have hzc : z ∈ Subgroup.center (PSL2 K) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rw [psl2_center_eq_bot K, Subgroup.mem_bot] at hzc
    exact hzc
  conj3 := conj3_of_cyclic_sylow fun P => isCyclic_sylow_three_psl2 h3 (by omega) P
  inner3 α hα := by
    by_cases hin : IsInnerAut α
    · obtain ⟨x, hx⟩ := hin
      refine ⟨x, fun y => ?_⟩
      rw [← hx]
      simp only [MulAut.conj_apply]
      convert Subgroup.one_mem _ using 1
      group
    · exfalso
      obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, hd, hαd⟩ := isField_of_pow_three_of_not_inner hα hin
      have hφ3 : (psl2FieldAut K σ) ^ 3 = 1 := by
        have h1 : α ^ 3 = d * (psl2FieldAut K σ) ^ 3 * d⁻¹ := by rw [hαd, conj_pow]
        rw [hα] at h1
        have h2' : (psl2FieldAut K σ) ^ 3 = d⁻¹ * 1 * d := by
          rw [h1]; group
        rw [h2']; group
      have hσ3 : σ ^ 3 = 1 :=
        psl2FieldAut_injective K (by rw [map_pow, map_one]; exact hφ3)
      exact hφ1 (by rw [hσ σ hσ3, map_one])

theorem GoodGroup.sl2 (hodd : Odd (Nat.card K)) (h3 : ringChar K ≠ 3)
    (h5 : 5 ≤ Nat.card K) (hσ : ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ = 1) : GoodGroup SL(2, K) :=
  GoodGroup.of_central_quotient (CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 (by omega))
    (by rw [CFSG.ClassicalInvolution.sl2_natCard_center hodd]; decide)
    ⟨sl2Three K, sl2Three_ne_one, sl2Three_pow_three⟩ (GoodGroup.psl2 h3 h5 hσ)

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
