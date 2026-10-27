module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)

section Inputs

@[expose] def E6SwapCoverCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂), 4 ≤ Nat.card (fixSubfield σ) →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), t ∈ centralizer (L : Set G) →
    t * t = 1 → (∀ N : E6Neighbour, Nonempty (SwapFactorCover e t N)) →
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      Nonempty (G₁ ⧸ center G₁ ≃* adjointGroup .E6 (fixSubfield σ)) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e

@[expose] def E6SwapConjGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    RootSwapKind e t →
    ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      Nonempty (G₁ ⧸ center G₁ ≃* adjointGroup .E6 (fixSubfield σ)) →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e →
      ∀ h : G, t ∈ normalizer (CFSG.conjugate (pieceSup e) h : Set G) →
        CFSG.conjugate (pieceSup e) h ≤
          ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
            perfectCore (CFSG.conjugate (pieceSup e) h ⊓
              centralizer (modelToG e (leviTorus (fixSubfield σ) J.1) : Set G))

end Inputs

section Reductions

theorem e6SwapRowCTInput_of_swapCoverCT (hCT : E6SwapCoverCTInput) : E6SwapRowCTInput := by
  intro G _ _ L K₂ _ _ _ σ f _ hf e t hw hk
  have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  exact hCT G L K₂ σ h4 e t hw.mem_centralizer htt (nonempty_forall_swapFactorCover hw hf e hk)

theorem e6SwapRowUniqueInput_of_conjGen (hU : E6SwapConjGenInput) : E6SwapRowUniqueInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw hk G₁ hqs hiso h₁₂ hsup
  exact F4Pilot.unique_of_forall_conjugate_generation
    (J := fun J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} =>
      modelToG e (leviTorus (fixSubfield σ) J.1))
    (fun J => pieceCore_le_pieceSup J) (hU G L K₂ σ f hq hf e t hw hk G₁ hqs hiso h₁₂ hsup)

end Reductions

end CFSG.SeitzReduction.E6Pilot
