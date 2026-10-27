module

public import CFSG.GH74.GLS.IVK.Prod32.LangFixedAux2
public import CFSG.GH74.GLS.IVK.Prod32.LangFixedAux3

public section

namespace CFSG.GH74.GLS.IVK.Prod3.LangF

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

section Final

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem card_fixedField {r : ℕ} (hF₂ : Nat.card F₂ = r ^ 4) :
    Nat.card (fixedField σ₂) = r ^ 2 := by
  have h1 := fixedField_card_pow σ₂
  rw [h.σ₂_ord, hF₂] at h1
  have h2 : (Nat.card (fixedField σ₂)) ^ 2 = (r ^ 2) ^ 2 := by rw [h1]; ring
  exact Nat.pow_left_injective (by norm_num) h2

theorem pgl2_quot {r : ℕ} (hF₂ : Nat.card F₂ = r ^ 4) :
    ∃ _ : ((cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a)).Normal,
      IsPGL2 (↥(cen (K₁ ⊔ K₂) a) ⧸ (cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a))
        (fun q => q = r ^ 2) := by
  have hN := cen_normal₁ h
  refine ⟨hN, ↥(fixedField σ₂), inferInstance, inferInstance, card_fixedField h hF₂, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq (ker_psi h).symm).trans
    ((QuotientGroup.quotientKerEquivRange (psi h)).trans
      ((MulEquiv.subgroupCongr (range_psi h)).trans
        (MonoidHom.ofInjective (pgl2Incl_injective σ₂)).symm))

end Final

end CFSG.GH74.GLS.IVK.Prod3.LangF

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup

section Main

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

theorem LangHyp.fixed (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {r : ℕ} (hr : 3 ≤ r)
    (hF₁ : Nat.card F₁ = r ^ 4) (hF₂ : Nat.card F₂ = r ^ 4) : Ch K₁ K₂ a r := by
  refine ⟨LangF.eLayer_cen_sup h hr hF₁ hF₂, ?_⟩
  intro K hK
  rcases hK with rfl | hK
  · rw [LangF.eLayer_cen₁ h hr hF₁]
    exact ⟨LangF.hasSL2Model_cen₁ h hF₁, LangF.pgl2_quot h hF₂⟩
  · rw [Set.mem_singleton_iff] at hK
    subst hK
    rw [LangF.eLayer_cen₁ (LangF.symm h) hr hF₂]
    refine ⟨LangF.hasSL2Model_cen₁ (LangF.symm h) hF₂, ?_⟩
    have := LangF.pgl2_quot (LangF.symm h) hF₁
    rwa [sup_comm] at this

end Main

end CFSG.GH74.GLS.IVK.Prod3
