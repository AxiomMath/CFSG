module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrFinal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrFacts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDCover

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

theorem orderOf_negOneR {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0)
    (h2 : (2 : F) ≠ 0) : orderOf (negOneR hS) = 2 := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  exact orderOf_eq_prime (by rw [pow_two]; exact spinGroup.negOne_mul_self _ _)
    (spinGroup.negOne_ne_one _ _)

theorem eq_negOneR_of_isCyclic {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q₀ : QuadraticForm F (σ → F)} {Q0 : (σ → F) → F} (hS : SpinFacts Q₀ Q0)
    (h2 : (2 : F) ≠ 0) (hcyc : IsCyclic (center (spinGroup Q₀)))
    (hcard : Nat.card (center (spinGroup Q₀)) ∣ 4) {x₀ : spinGroup Q₀}
    (hx₀Z : x₀ ∈ center (spinGroup Q₀)) (hx₀2 : orderOf x₀ = 2) : x₀ = negOneR hS := by
  have : Finite (spinGroup Q₀) := hS.finite
  obtain ⟨-, hZ2⟩ := center_hyps_of_isCyclic hcyc hcard (negOneR_mem_center hS)
    (orderOf_negOneR hS h2)
  rcases hZ2 x₀ hx₀Z (by rw [← hx₀2, pow_orderOf_eq_one]) with h | h
  · rw [h, orderOf_one] at hx₀2
    exact absurd hx₀2 (by norm_num)
  · exact h

theorem burgoynePropBDrExcInput_of_klein (hklein : BurgoynePropBSpinPlusKleinInput) :
    BurgoynePropBDrExcInput := by
  intro J _ _ K _ t Y c hH τ n p f hτ hL F _ _ hF hFc R hR hRform θ g hσ hg hpc
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : Fintype F := Fintype.ofFinite F
  rcases hτ with rfl | ⟨rfl, hn5⟩
  ·
    rcases hRform with ⟨h, -⟩ | ⟨-, hn1, b, c₀, hirr, hRQ⟩
    · exact absurd h (by decide)
    have hmod : StatedClassicalModel (GeneralizedFitting.subgroup (rhoZ K).range)
        .POmegaMinus n p f := by
      rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
      · exact hcl
      all_goals exact absurd htag (by decide)
    have hn4 : 4 ≤ n := hmod.1.2.2
    have : Fact p.Prime := ⟨hmod.1.1⟩
    have hf : 1 ≤ f := hmod.1.2.1
    have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hp2 : p ≠ 2 := by rw [← ringChar.eq F p]; exact hF
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c₀ v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    let e' : GeneralizedFitting.subgroup (rhoZ K).range ≃*
        StatedProj (StatedOmega (StatedQuadMinus n F b c₀)) :=
      θ.trans ((oTransport 1 1 hS₁).symm.trans (statedProjectiveReindexEquiv
        (minusIndexEquiv n hn1) (quadMinus n F b c₀) (coe_quadMinus n F b c₀)).symm)
    have hker := (oKer_coordinateMinus hmod F hFc b c₀ hirr e').transport 1 1 hS₁
    have hsurj := (oSurj_coordinateMinus hmod F hFc b c₀ hirr e').transport 1 1 hS₁
    have hS := spinFacts_quadMinus hirr hF hn4 hFc
    refine exc_false_of_facts K hH hp2 hf hFc hS (by omega) (minusIndexEquiv n hn1) hR hker
      hsurj hS₁ θ (fun x₀ hx₀Z hx₀2 _ => ?_) hg hσ hpc
    obtain ⟨hcyc, hcard⟩ := isCyclic_center_quadMinus hirr hn4 hFc
    exact eq_negOneR_of_isCyclic hS h2 hcyc hcard hx₀Z hx₀2
  ·
    rcases hRform with ⟨-, hRQ⟩ | ⟨h, -⟩
    swap
    · exact absurd h (by decide)
    have hmod : StatedClassicalModel (GeneralizedFitting.subgroup (rhoZ K).range)
        .POmegaPlus n p f := by
      rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
      · exact hcl
      all_goals exact absurd htag (by decide)
    have : Fact p.Prime := ⟨hmod.1.1⟩
    have hf : 1 ≤ f := hmod.1.2.1
    have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hp2 : p ≠ 2 := by rw [← ringChar.eq F p]; exact hF
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    let e' : GeneralizedFitting.subgroup (rhoZ K).range ≃*
        StatedProj (StatedOmega (StatedQuadPlus n F)) :=
      θ.trans ((oTransport 1 1 hS₁).symm.trans (statedProjectiveReindexEquiv
        (plusIndexEquiv n) (quadPlus n F) (coe_quadPlus n F)).symm)
    have hker := (oKer_coordinatePlus hmod F hFc e').transport 1 1 hS₁
    have hsurj := (oSurj_coordinatePlus hmod F hFc hn5 e').transport 1 1 hS₁
    have hS := spinFacts_quadPlus hF (by omega : 3 ≤ n)
    have : Finite (spinGroup (quadPlus n F)) := hS.finite
    refine exc_false_of_facts K hH hp2 hf hFc hS (by omega) (plusIndexEquiv n) hR hker hsurj
      hS₁ θ (fun x₀ hx₀Z hx₀2 hII => ?_) hg hσ hpc
    rcases Nat.even_or_odd n with hev | hodd
    · have hn6 : 6 ≤ n := by
        obtain ⟨k, hk⟩ := hev
        omega
      exact hklein F hF n hn6 hev _ (MonoidHom.id _) Function.surjective_id x₀ hII
    · obtain ⟨hcyc, hcard⟩ := isCyclic_center_quadPlus hF (by omega) hodd
      exact eq_negOneR_of_isCyclic hS h2 hcyc hcard hx₀Z hx₀2

end CFSG.ComponentClassification.Burgoyne.DX.Dr
