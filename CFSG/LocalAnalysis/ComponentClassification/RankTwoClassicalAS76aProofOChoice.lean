module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviInner
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofONoInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOTheta
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem card_center_statedOmega_eq_one {K : Type} [Field K] {κ : Type} [Fintype κ]
    [DecidableEq κ] {R : (κ → K) → K}
    (hc : center (StatedOmega R) = (StatedScalars κ K).subgroupOf (StatedOmega R))
    (hinj : Function.Injective (oProj R)) : Nat.card (center (StatedOmega R)) = 1 := by
  have h : (StatedScalars κ K).subgroupOf (StatedOmega R) = ⊥ := by
    rw [← QuotientGroup.ker_mk' ((StatedScalars κ K).subgroupOf (StatedOmega R))]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hinj
  rw [hc, h, Subgroup.card_bot]

section Choice

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

theorem leviChoice_orth_of {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A))) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q)) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hqs : CFSG.IsQuasisimple (StatedOmega Q₂)) (hZ₂ : Odd (Nat.card (center (StatedOmega Q₂))))
    {D : ClassicalModel A} {p : G} (hq : D.q = 2 ^ m) {T : Set G} (hαD : D.alpha p = closure T)
    (hT : ∀ y ∈ T, y ∈ liftSub θ (oBarL oe hQ) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    (hlevi : D.LeviType (levLift θ (oBarL oe hQ)))
    (hnoInv : ∀ β : MulAut (StatedProj (StatedOmega Q)), β * β = 1 →
      (∀ x ∈ oBarTwo oe hQ hSL, β x = x) → (∀ x ∈ oBarOne oe hQ hSL, β x = x) →
        (∀ x ∈ oBarL oe hQ, β x = x) → β = 1)
    (h5 : ¬ D.IsLinearFiveFour) (h4 : ¬ D.IsLTwoFour) :
    LeviChoice D p (levLift θ (oBarTwo oe hQ hSL))
      (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarOne oe hQ hSL)) := by
  have hlayer := layerCentralizer_eq_oLeviL_of_le hker hθ hinj ht0 ht1 hperf hqs le_rfl
    (oLevi_Y_le (oe := oe) (hQ := hQ) (hSL := hSL) (θ := θ))
  refine
    { W_le := le_sup_left
      Y_le := ?_
      W_type := ⟨K, inferInstance, inferInstance, by rw [hK, hq],
        nonempty_oLeviW_equiv hm hK hker hθ hZ hinj⟩
      alpha_le := ?_
      quasisimple := ?_
      oddCenter := ?_
      levi := ?_
      noInv := ?_
      diag := fun h => (h5 h).elim
      outerFree := fun h => (h4 h).elim
      sym := fun h => (h4 h).elim }
  · rw [hαD]
    exact oLevi_Y_le_centralizer hker hZ hT oLevi_Y_le
  · rw [hαD, hlayer]
    exact oLevi_alpha_le hker hθ hZ hperf hT
  · rw [hlayer]
    exact isQuasisimple_oLeviL hker hθ hinj hperf hqs
  · rw [hlayer]
    exact odd_card_center_oLeviL hker hθ hZ hinj hperf hZ₂
  · rw [hlayer]
    exact hlevi
  · rw [hlayer]
    exact noInv_oLevi hA hker hθ hperf hnoInv

end Choice

end CFSG.ComponentClassification.RankTwoClassical
