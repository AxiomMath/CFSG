module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterInvolutions

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)
open CFSG.ComponentClassification.CatalogueBSmallRee (small_Ree_automorphism_involutions_inner)

theorem small_Ree_model_involutions_inner (L : Type) [Group L] (p f : ℕ)
    (h : ReeTitsModel L .twistedG2 p f) (α : MulAut L) (hα : α ^ 2 = 1) : α ∈ inner L := by
  obtain ⟨-, -, hp, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := small_Ree_model_Schreier L p f h
  obtain ⟨-, a, hfa, K, _, _, hK, he⟩ := h
  subst hp
  have ha : 1 ≤ a := by omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK he
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  by_cases h1 : α = 1
  · rw [h1]
    exact one_mem _
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα h1
  have hβ : orderOf (MulAut.congr E α) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hα2
  obtain ⟨z, ⟨-, hz⟩, -⟩ := (small_Ree_automorphism_involutions_inner a ha K hK').2 _ hβ
  refine ⟨E.symm z, (MulAut.congr E).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, ← hz]

end CFSG.LocalAnalysis.ComponentInitial
