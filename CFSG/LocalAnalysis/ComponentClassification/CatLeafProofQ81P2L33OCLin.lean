module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCLinInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCLinGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Odd

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem not_isPGroup_projectiveSL {p f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (α : MulAut (projectiveSL n K)) (hα : orderOf α = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  have : CharP K p := GSThmB.Cent516.charP_of_card hp hK
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn).2 α
  by_cases hσ : σ = 1
  · subst hσ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · have h' : α = conjAut n K A := by rw [hαeq, map_one, mul_one, pow_zero, mul_one]
      subst h'
      exact not_isPGroup_of_fixed_odd (exists_fixed_odd_conjAut hp hp2 hn A hα2)
    · have h' : α = conjAut n K A * dualAut n K := by rw [hαeq, map_one, mul_one, pow_one]
      subst h'
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut hn A hα2 with hA | hA
      · exact not_isPGroup_of_fixed_odd
          (exists_fixed_odd_conjAut_dualAut_of_transpose_eq hp hp2 hn A hA)
      · exact not_isPGroup_of_fixed_odd
          (exists_fixed_odd_conjAut_dualAut_of_transpose_eq_neg hp hp2 hn A hA)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · have h' : α = conjAut n K A * fieldAut n K σ := by rw [hαeq, pow_zero, mul_one]
      subst h'
      exact not_isPGroup_of_fixed_perfect
        (exists_fixed_perfect_even_conjAut_fieldAut hp hf hK hn A σ hσ hα2)
    · have h' : α = conjAut n K A * fieldAut n K σ * dualAut n K := by rw [hαeq, pow_one]
      subst h'
      exact not_isPGroup_of_fixed_perfect
        (exists_fixed_perfect_even_conjAut_fieldAut_dualAut hp hp2 hf hK hn A σ hσ hα2)

theorem oddClsRow_psl : OddClsRow .PSL := by
  refine oddClsRow_psl_of fun Y _ _ hY _ _ a ha hP => ?_
  obtain ⟨n, p, f, hn, hp2, ⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hY
  set e' : Y ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K) with he'
  have : Finite (projectiveSL n K) := Finite.of_equiv _ e'.toEquiv
  exact absurd (L33.isPGroup_fixedPoints_congr e' a hP)
    (not_isPGroup_projectiveSL hp hp2 hf hn hK _ ((L33.orderOf_congr e' a).trans ha))

end CFSG.ComponentClassification.HarrisLit.L33.OC
