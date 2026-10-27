module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4GraphFixed
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4Diag
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4ThreeStmt
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.GraphCorrespondenceAux.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.NormalPi

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

set_option linter.unusedSectionVars false


theorem d4_cent_graphOne {K : Type} [Field K] [Finite K] [CharP K 3]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hαdef : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))
    (hα3 : α ^ 3 = 1) :
    ∀ w : MulAut (adjointGroup Tag.D4 K), Nat.Coprime 3 (orderOf w) → w * α = α * w →
      (∀ x ∈ fixSubgroup α, w x = x) → w ∈ innerAut (adjointGroup Tag.D4 K) := by
  intro w hcop hcomm hfix
  have hcomm' : w * (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) * w := by
    rw [← hαdef]
    exact hcomm
  obtain ⟨c, b, σ, hΞ⟩ := exists_normalAut_of_commute_graphOne g a w hcop hcomm'
  have hσ : σ = 1 := d4_sigma_eq_one g a α hαdef hα3 c b σ w hΞ hcop hcomm hfix
  subst hσ
  rw [hΞ] at hcomm' ⊢
  exact d4_commute_diag_inner g c a b hcomm'

theorem outerCentData_d4_graphOne {K : Type} [Field K] [Finite K] [CharP K 3]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hαdef : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))
    (hα3 : α ^ 3 = 1) : OuterCentData 3 α := by
  haveI : Finite (adjointGroup Tag.D4 K) := by
    haveI : Finite (ModGL Tag.D4 K) := finite_modGL
    infer_instance
  exact OuterCentData.ofFixedData (d4_fixedData_graphOne g a α hαdef hα3)
    (d4_cent_graphOne g a α hαdef hα3)

theorem d4ThreeGraphCent_holds : D4ThreeGraphCent := by
  intro K _ _ _ g a ε hε0 hε3 α hα hα3
  have hrefl : (RingEquiv.refl K) = (1 : K ≃+* K) := rfl
  rw [hrefl] at hα
  interval_cases ε
  · exact outerCentData_d4_graphOne g a α hα hα3
  · obtain ⟨g', a', hinv⟩ := GraphCorrespondence.inv_normalForm g a
    rw [← hα] at hinv
    exact OuterCentData.of_inv (outerCentData_d4_graphOne g' a' α⁻¹ hinv
      (by rw [inv_pow, hα3, inv_one]))

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
