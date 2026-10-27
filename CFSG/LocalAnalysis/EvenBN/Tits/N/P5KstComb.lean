module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstPerm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Equiv Finset

@[expose] def FixVec (σ : Perm (Fin 6)) : Finset (Fin 6 → ZMod 2) :=
  univ.filter fun f => (fun i => f (σ⁻¹ i)) = f ∨ (fun i => f (σ⁻¹ i)) = f + 1

@[expose] def EvenVec : Finset (Fin 6 → ZMod 2) := univ.filter fun f => ∑ i, f i = 0

theorem card_fixVec : ∀ σ : Perm (Fin 6), σ * σ = 1 → (fixCount σ = 0 ∨ fixCount σ = 2) →
    (FixVec σ).card = 16 := by
  decide +kernel

theorem card_fixVec_even : ∀ σ : Perm (Fin 6), σ * σ = 1 → (fixCount σ = 0 ∨ fixCount σ = 2) →
    (FixVec σ ∩ EvenVec).card = 8 := by
  decide +kernel

theorem card_fixVec_inter_aux :
    ∀ σ ∈ (univ.filter fun σ : Perm (Fin 6) =>
        σ * σ = 1 ∧ σ ≠ 1 ∧ (fixCount σ = 0 ∨ fixCount σ = 2)),
      ∀ τ ∈ (univ.filter fun τ : Perm (Fin 6) =>
        τ * τ = 1 ∧ τ ≠ 1 ∧ (fixCount τ = 0 ∨ fixCount τ = 2)),
      σ * τ = τ * σ → σ ≠ τ → (fixCount (σ * τ) = 0 ∨ fixCount (σ * τ) = 2) →
        (FixVec σ ∩ FixVec τ).card ≤ 8 := by
  decide +kernel

theorem card_fixVec_inter {σ τ : Perm (Fin 6)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hc : σ * τ = τ * σ) (hne : σ ≠ τ) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hfσ : fixCount σ = 0 ∨ fixCount σ = 2) (hfτ : fixCount τ = 0 ∨ fixCount τ = 2)
    (hfστ : fixCount (σ * τ) = 0 ∨ fixCount (σ * τ) = 2) :
    (FixVec σ ∩ FixVec τ).card ≤ 8 := by
  refine card_fixVec_inter_aux σ ?_ τ ?_ hc hne hfστ
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ, hσ1, hfσ⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hτ, hτ1, hfτ⟩

theorem even_pair : ∀ f : Fin 6 → ZMod 2, ∑ i, f i = 0 → f ≠ 0 → f ≠ 1 →
    ∃ p q : Fin 6, p ≠ q ∧
      (f = Pi.single p 1 + Pi.single q 1 ∨ f + 1 = Pi.single p 1 + Pi.single q 1) := by
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
