module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow

theorem not_oddLieOrder_443520 :
    ¬ CFSG.ComponentClassification.HarrisLit.T1.SporRow.OddLieOrder 443520 :=
  not_oddLieOrder_of_check (l := [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide)
    (by decide +kernel)

section Certified


theorem false_of_oddLie
    {J : Type} [Group J] {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible τ n p f) (hJ : CFSG.Blueprint.LieModel J τ n p f) {α : MulAut J}
    (hα : orderOf α = 2) {K : Subgroup (fixedSubgroup α)} (hK : CFSG.IsComponent K)
    (hcard : Nat.card (K ⧸ Subgroup.center K) = 443520) : False := by
  rcases CFSG.ComponentClassification.CatLeafProof.gls3OddLieAutComponentsInput_holds J τ n p f
      hadm.1 hp2 hadm hJ α hα K hK with ⟨τ', n', f', -, hmodel⟩ | ⟨-, -, -, hmodel⟩
  · exact not_oddLieOrder_443520
      (hcard ▸ oddLieOrder_of_lieModel hadm.1 hp2 hmodel)
  · have hadmPSL : StatedLieAdmissible .PSL 2 2 3 := by
      refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
    obtain ⟨-, hord, -⟩ :=
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSL 2 2 3 hadmPSL hmodel
    have hdiv : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have hnum : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [hdiv, hnum, mul_one] at hord
    have hdvd : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card K :=
      Subgroup.card_quotient_dvd_card (Subgroup.center K)
    rw [hcard, hord] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

end Certified

end CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof
