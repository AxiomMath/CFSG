module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveA4Pure
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFrameData

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem E8FiveSq.rootChar_pow_five_of_mem {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (D : LangPlaneData Tag.E8 K E₀) {x : adjointGroup Tag.E8 K} (hx : x ∈ E₀)
    {a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E8 a = diagMap D x)
    (v : Fin Tag.E8.rank → ℤ) : rootChar a v ^ 5 = 1 := by
  have h := E8FiveSq.pow_five_eq_one_of_rootDiagUnit_eq hE₀p D hx ha
  exact CTTorus.rootChar_pow_eq_one (fun i => by simpa using congrFun h i) v

theorem e8FiveOneClosing_holds : E8FiveOneClosing := by
  intro K _ _ hK E₀ hE₀p hE₀c D hreg hw
  have hK1 : 0 < Nat.card K := Nat.card_pos
  have hpK : ¬ 5 ∣ Nat.card K := by omega
  obtain ⟨F⟩ := nonempty_e8FiveFrameElt_split K hK
  refine E8FiveSq.planeCl_eq_top_of_frameElt hpK hE₀p hE₀c D hreg hw ?_ F
  intro x hx a ha v
  rw [E8FiveSq.rootChar_smul_eq_pow_of_mem D hx ha v]
  obtain ⟨m, hm⟩ := hK
  rw [show Nat.card K = 5 * m + 1 by omega, pow_succ, pow_mul,
    E8FiveSq.rootChar_pow_five_of_mem hE₀p D hx ha v, one_pow, one_mul]

theorem e8FiveTwoClosing_holds : E8FiveTwoClosing := by
  intro K _ _ hK E₀ hE₀p hE₀c D hreg hw
  have hpK : ¬ 5 ∣ Nat.card K := by omega
  obtain ⟨F⟩ := nonempty_e8FiveFrameElt_twisted K hK
  obtain ⟨w₀, hw₀⟩ := E8FiveSq.exists_weyl_neg_E8_five
  refine E8FiveSq.planeCl_eq_top_of_frameElt (V := w₀ * D.w) hpK hE₀p hE₀c D hreg ?_ ?_ F
  · intro h1
    obtain ⟨u, hu⟩ := hw
    apply hu
    rw [eq_inv_of_mul_eq_one_right h1, inv_smul_eq_iff, hw₀, neg_neg]
  · intro x hx a ha v
    rw [mul_smul, hw₀, ← neg_one_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, zpow_neg_one,
      E8FiveSq.rootChar_smul_eq_pow_of_mem D hx ha v]
    obtain ⟨m, hm⟩ := hK
    have h5 := E8FiveSq.rootChar_pow_five_of_mem hE₀p D hx ha v
    rw [show Nat.card K = 5 * (m - 1) + 4 by omega, pow_add, pow_mul, h5, one_pow, one_mul,
      inv_eq_iff_mul_eq_one, ← pow_succ]
    exact h5

end CFSG.LieType.SeitzGeneration.ExcHigh
