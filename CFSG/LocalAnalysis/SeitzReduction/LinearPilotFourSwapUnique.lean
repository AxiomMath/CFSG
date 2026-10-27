module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LinearSwapFactorNormalFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (_ : L ≃* LinearFlag.projectiveSL 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
    ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
      t ∈ normalizer (A : Set G) →
      t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
      t ∉ centralizer (A : Set G) →
      t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False

theorem linearSwapRowUniqueFourInput_of_factorNormal (hN : LinearSwapFactorNormalFourInput) :
    LinearSwapRowUniqueFourInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt _ G₁ hq h₁₂ hsup hδ hsurj
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  refine unique_of_swapFactors (m := 3) hset (by norm_num) hK4 e htC ht hq h₁₂ hsup hδ hsurj
    fun h htA htB hnA hnB => ?_
  have hBconj := map_conj_conjugate_eq (A := G₁) h t
  refine hN G L hset f K hKc hf e t ht hKt (CFSG.conjugate G₁ h)
    (isQuasisimple_conjugate hq h)
    (exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj h) (h⁻¹ * t * h) ?_ htA ?_ hnA ?_
  · rw [hBconj]
    exact conjugate_le_centralizer_of_le_centralizer h₁₂ h
  · rw [hBconj]
    exact htB
  · rw [hBconj]
    exact hnB

section Inputs


theorem linearFourInput_of_factorNormal (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInputAt 3) (hSpor : CatSLmSporadicAt 3)
    (hN : LinearSwapFactorNormalFourInput) : LinearFourInput :=
  linearFourInput_of_inputs hGLS hX hSpor (linearSwapRowUniqueFourInput_of_factorNormal hN)

end Inputs

end CFSG.SeitzReduction.LinearPilot
