module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.KleinBasic

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (τ : K ≃+* K) : τ = 1 := by
  have hsub : Subsingleton Kˣ := by
    have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp h).1
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have h1 : x = 1 := by
      have := Subsingleton.elim (Units.mk0 x hx) 1
      exact congrArg (fun u : Kˣ => (u : K)) this
    simp [h1]

theorem conjAut_mem_range_of_card_two (hK : Nat.card K = 2) (A : GL (Fin n) K) :
    conjAut n K A ∈
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hsub : Subsingleton Kˣ := by
    have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp h).1
  have hdet : GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have hdet' : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hdet
    simpa using this
  let g : SpecialLinearGroup (Fin n) K := ⟨(A : Matrix (Fin n) (Fin n) K), hdet'⟩
  have hg : SpecialLinearGroup.toGL g = A := by
    ext1
    rfl
  exact ⟨proj n K g, by rw [← conjAut_toGL, hg]⟩

theorem not_outerKlein_projectiveSL_two (hK : Nat.card K = 2) (hn : 3 ≤ n)
    (σ : MulAut (projectiveSL n K)) : ¬ OuterKlein σ := by
  rintro ⟨α, β, -, -, -, -, -, hα, hβ, hαβ⟩
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  have htrans := standard_automorphism_transport (K := K) (n := n)
  obtain ⟨A, τ, ε, hε, hAα⟩ := hgen α
  obtain ⟨B, τ', ε', hε', hBβ⟩ := hgen β
  rw [ringEquiv_eq_one_of_card_two hK τ, map_one, mul_one] at hAα
  rw [ringEquiv_eq_one_of_card_two hK τ', map_one, mul_one] at hBβ
  interval_cases ε
  · rw [pow_zero, mul_one] at hAα
    exact hα (hAα ▸ conjAut_mem_range_of_card_two hK A)
  · interval_cases ε'
    · rw [pow_zero, mul_one] at hBβ
      exact hβ (hBβ ▸ conjAut_mem_range_of_card_two hK B)
    · rw [pow_one] at hAα hBβ
      apply hαβ
      have h : α * β = conjAut n K (A * GeneralLinearGroup.inverseTranspose B) := by
        rw [hAα, hBβ, map_mul, ← htrans.2.2.2.2.1 B]
        group
      rw [h]
      exact conjAut_mem_range_of_card_two hK _

end Linear

theorem harrisKleinFree_PSL_two_one {n : ℕ} (hn : 3 ≤ n) : HarrisKleinFree .PSL n 2 1 := by
  refine harrisKleinFree_of_concrete fun S _ _ hm => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)
  have hK2 : Nat.card K = 2 := by simpa using hK
  have e' : S ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact ⟨projectiveSL n K, inferInstance, e', fun σ => not_outerKlein_projectiveSL_two hK2 hn σ⟩

theorem harrisKleinFree_PSL_four_two_one : HarrisKleinFree .PSL 4 2 1 :=
  harrisKleinFree_PSL_two_one (by norm_num)

theorem harrisKleinFree_PSL_five_two_one : HarrisKleinFree .PSL 5 2 1 :=
  harrisKleinFree_PSL_two_one (by norm_num)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
