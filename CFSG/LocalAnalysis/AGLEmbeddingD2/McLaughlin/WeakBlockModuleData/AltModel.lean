module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModelBridge
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Combinatorics.Pigeonhole

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv Equiv.Perm

instance altPermAction (N : ℕ) :
    MulAction (alternatingGroup (Fin N)) (Fin N → ZMod 2) where
  smul σ f := fun i => f ((σ : Perm (Fin N))⁻¹ i)
  one_smul f := by funext i; rfl
  mul_smul σ τ f := by funext i; rfl

theorem threeFixedModel_altPerm {N : ℕ} (hN : 5 ≤ N) :
    ThreeFixedModel (alternatingGroup (Fin N)) (Fin N → ZMod 2) := by
  intro f
  have key : ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by
    obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f
      (n := 2) (by simp [ZMod.card]; omega)
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    exact ⟨a, b, c, hab, hac, hbc, ha.trans hb.symm, ha.trans hc.symm⟩
  obtain ⟨a, b, c, hab, hac, hbc, hfb, hfc⟩ := key
  set σ : Perm (Fin N) := swap a b * swap a c with hσ
  have h3 : σ.IsThreeCycle := isThreeCycle_swap_mul_swap_same hab hac hbc
  have hout : ∀ x, ¬ (x = a ∨ x = b ∨ x = c) → σ x = x := by
    intro x hx
    have hxa : x ≠ a := fun h => hx (Or.inl h)
    have hxb : x ≠ b := fun h => hx (Or.inr (Or.inl h))
    have hxc : x ≠ c := fun h => hx (Or.inr (Or.inr h))
    simp [hσ, Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxc,
      swap_apply_of_ne_of_ne hxa hxb]
  have hfT : ∀ x, (x = a ∨ x = b ∨ x = c) → f x = f a := by
    rintro x (rfl | rfl | rfl)
    · rfl
    · exact hfb.symm
    · exact hfc.symm
  refine ⟨⟨σ, h3.mem_alternatingGroup⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact h3.orderOf
  · funext i
    change f ((σ⁻¹) i) = f i
    by_cases hi : i = a ∨ i = b ∨ i = c
    · have hin : σ⁻¹ i = a ∨ σ⁻¹ i = b ∨ σ⁻¹ i = c := by
        by_contra h
        have h1 := hout _ h
        have h2 : σ (σ⁻¹ i) = i := by simp
        rw [h2] at h1
        exact h (h1 ▸ hi)
      rw [hfT _ hin, hfT _ hi]
    · have : σ⁻¹ i = i := by
        rw [Perm.inv_eq_iff_eq]
        exact (hout i hi).symm
      rw [this]

@[expose] def IsAltPermSubImage (Γ W : Type*) [Group Γ] [MulAction Γ W] (N : ℕ) : Prop :=
  ∃ (e : alternatingGroup (Fin N) ≃* Γ) (X : Set (Fin N → ZMod 2)) (π : (Fin N → ZMod 2) → W),
    (∀ w, ∃ f ∈ X, π f = w) ∧
    ∀ (g : alternatingGroup (Fin N)) (f : Fin N → ZMod 2), f ∈ X → π (g • f) = e g • π f

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
