module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCore5

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Stated

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q₀ : (ι → K) → K}
  {Q₂₀ : (ι₂ → K) → K} {Qf : QuadraticForm K (ι → K)} {Q₂f : QuadraticForm K (ι₂ → K)}
  (hQf : ⇑Qf = Q₀) (hQ₂f : ⇑Q₂f = Q₂₀)
  (hQ : ∀ v, Q₀ v = Q₂₀ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤) {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q₀)}
include hQf hQ₂f

theorem rigidCore_orth_four_stated (hperf₂ : commutator (StatedOmega Q₂₀) = ⊤) [Nonempty ι₂]
    (hnd : Q₂f.polarBilin.Nondegenerate)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega Q₂₀, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    (hO₂ : NoNormalTwo (StatedOmega Q₂₀)) (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K)))
    (hK : 4 ≤ Nat.card K)
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂₀, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂₀ (d • w) = d * d * Q₂₀ w) {w₀ : ι₂ → K} (hw₀ : Q₂₀ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hinj : Function.Injective (oProj Q₀))
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = oProj Q₀ (oRhoOne oe hQ hSL (slTr 1))) :
    RigidCore A p (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ)) := by
  subst hQf hQ₂f
  exact rigidCore_orth_four hQ hSL hperf₂ hnd hfix hO₂ hSL₂ hK hcomm hsm hw₀ ht0 ht1 hinj hθ
    hker hodd hpA hp2 hθp

theorem rigidCore_orth_five_stated {ι₃ : Type} [Fintype ι₃] [DecidableEq ι₃]
    {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂} {Q₃₀ : (ι₃ → K) → K} {Q₃f : QuadraticForm K (ι₃ → K)}
    (hQ₃f : ⇑Q₃f = Q₃₀)
    (hQ₂ : ∀ w, Q₂₀ w = Q₃₀ (fun a => w (oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
    (hperf₂ : commutator (StatedOmega Q₂₀) = ⊤) (hnd : Q₂f.polarBilin.Nondegenerate)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega Q₂₀, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    (hO₂ : NoNormalTwo (StatedOmega Q₂₀)) (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K)))
    (hsimpSL : IsSimpleGroup SL(2, K)) (hsimp : IsSimpleGroup ↥(StatedOmega Q₂₀))
    (hcard : Nat.card ↥(StatedOmega Q₂₀) ≠ Nat.card SL(2, K)) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (hinj : Function.Injective (oProj Q₀))
    (hNN : NoNormalTwo (centralizer ((((oProj Q₀).comp ((oKappa oe hQ).comp
      (oRhoTwo oe₂ hQ₂ hSL))).range ⊔ ((oProj Q₀).comp ((oKappa oe hQ).comp
        (oRhoOne oe₂ hQ₂ hSL))).range : Subgroup _) : Set (StatedProj (StatedOmega Q₀)))))
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = oProj Q₀ (oRhoOne oe hQ hSL (slTr 1))) :
    RigidCore A p
      (levLift θ ((oProj Q₀).comp ((oKappa oe hQ).comp (oRhoTwo oe₂ hQ₂ hSL))).range ⊔
        levLift θ ((oProj Q₀).comp ((oKappa oe hQ).comp (oRhoOne oe₂ hQ₂ hSL))).range) := by
  subst hQf hQ₂f hQ₃f
  exact rigidCore_orth_five hQ hQ₂ hSL hperf₂ hnd hfix hO₂ hSL₂ hsimpSL hsimp hcard ht0 ht1 hinj
    hNN hθ hker hodd hpA hp2 hθp

end Stated

end CFSG.ComponentClassification.RankTwoClassical.ORigid
