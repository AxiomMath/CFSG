module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneHeisA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneGeo

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups commutatorElement
open Fin.NatCast

set_option linter.unusedSectionVars false


section Forms

variable {K : Type} [Field K] [Finite K]

theorem exists_eq_rootDiagUnit_mul_mA {y : ModGL Tag.E8 K} (hy : y ∈ monomialSubgroup Tag.E8 K)
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = e8FiveG1 ^ 4) :
    ∃ a : Fin Tag.E8.rank → Kˣ, y = rootDiagUnit Tag.E8 a * rhoA K coxSL5 := by
  obtain ⟨hm, hρ⟩ := exists_mA (K := K)
  have hx : y * (rhoA K coxSL5)⁻¹ ∈ monomialSubgroup Tag.E8 K := mul_mem hy (inv_mem hm)
  have h1 : weylQuotientHom Tag.E8 K ⟨_, hx⟩ = 1 := by
    have e : (⟨y * (rhoA K coxSL5)⁻¹, hx⟩ : monomialSubgroup Tag.E8 K) =
        ⟨y, hy⟩ * ⟨rhoA K coxSL5, hm⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hyw, hρ, mul_inv_cancel]
  obtain ⟨a, ha⟩ := CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup
    ((Four.weylQuotientHom_eq_one_iff hx).1 h1)
  exact ⟨a, by rw [ha]; group⟩

theorem du_geometric {ω : K} (hω : IsPrimitiveRoot ω 5) {yA yB : ModGL Tag.E8 K}
    (hyA : yA ∈ monomialSubgroup Tag.E8 K)
    (hyAw : weylQuotientHom Tag.E8 K ⟨yA, hyA⟩ = e8FiveG1 ^ 4) (du : Fin 5 → Kˣ)
    (hdu : ∀ A : SL(5, K), yB * rhoA K A * yB⁻¹ = rhoA K (conjDiagn du A))
    (hcomm : yA * yB = yB * yA) :
    ∃ s : Fin 5, ∀ i : Fin 5, (du i : K) = (du 0 : K) * ω ^ ((s : ℕ) * (i : ℕ)) := by
  have hrat : ∀ i j : Fin 5, i ≠ j →
      (du (i + 1) : K) * du j = du i * du (j + 1) := by
    intro i j hij
    obtain ⟨κ, hκ⟩ := exists_shift_scalar hyA hyAw i j hij
    set hij' : i + 1 ≠ j + 1 := (add_left_injective (1 : Fin 5)).ne hij with hij'def
    have h1 : yA * (yB * rhoA K (SpecialLinearGroup.transvection hij 1) * yB⁻¹) * yA⁻¹ =
        yB * (yA * rhoA K (SpecialLinearGroup.transvection hij 1) * yA⁻¹) * yB⁻¹ := by
      have : yA * yB * rhoA K (SpecialLinearGroup.transvection hij 1) * (yA * yB)⁻¹ =
          yB * yA * rhoA K (SpecialLinearGroup.transvection hij 1) * (yB * yA)⁻¹ := by
        rw [hcomm]
      simpa [mul_assoc] using this
    rw [hκ 1, hdu, hdu, conjDiagn_transvection, conjDiagn_transvection, hκ] at h1
    have h2 := tv_inj hij' (rhoA_injective h1)
    have hκ0 : (κ : K) ≠ 0 := κ.ne_zero
    simp only [Units.val_inv_eq_inv_val, mul_one] at h2
    have hdi : (du i : K) ≠ 0 := (du i).ne_zero
    have hdj : (du j : K) ≠ 0 := (du j).ne_zero
    have hdi1 : (du (i + 1) : K) ≠ 0 := (du (i + 1)).ne_zero
    have hdj1 : (du (j + 1) : K) ≠ 0 := (du (j + 1)).ne_zero
    field_simp at h2
    linear_combination -h2
  obtain ⟨lam, hlam5, hlam⟩ := geometric_of_ratio (fun i => (du i : K)) (fun i => (du i).ne_zero)
    hrat
  obtain ⟨s, hs5, hs⟩ := hω.eq_pow_of_pow_eq_one hlam5
  refine ⟨⟨s, hs5⟩, fun i => ?_⟩
  have := hlam i
  rw [this, ← hs, ← pow_mul]

end Forms

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
