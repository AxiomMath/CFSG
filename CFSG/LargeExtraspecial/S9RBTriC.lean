module

public import CFSG.LargeExtraspecial.S9RBType
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LargeExtraspecial.S9RBTriA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_sup_span_pair {V : Submodule (ZMod 2) S.Qt} {x y : S.Qt} (hx : x ∉ V)
    (hy : y ∉ V) (hxy : x + y ∉ V) :
    finrank (ZMod 2) ↥(V ⊔ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y) = finrank (ZMod 2) V + 2 := by
  have h1 : V ⊓ (ZMod 2) ∙ x = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvx⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_bot]
    rcases mem_span_cl_iff.mp hvx with h0 | h0
    · exact h0
    · exact absurd (h0 ▸ hvV) hx
  have h2 : (V ⊔ (ZMod 2) ∙ x) ⊓ (ZMod 2) ∙ y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvV, hvy⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_bot]
    rcases mem_span_cl_iff.mp hvy with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at hvV
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvV
      rcases mem_span_cl_iff.mp hb with hb0 | hb0
      · rw [hb0, add_zero] at hab
        exact hy (hab ▸ ha)
      · apply hxy
        have e : x + y = a + (x + x) := by rw [← hab, hb0]; abel
        rw [e, S8.add_self_zmod2, add_zero]
        exact ha
  have hx0 : x ≠ 0 := fun h => hx (h ▸ Submodule.zero_mem _)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ Submodule.zero_mem _)
  rw [finrank_sup_of_inf_eq_bot h2, finrank_sup_of_inf_eq_bot h1,
    finrank_span_singleton hx0, finrank_span_singleton hy0]

variable (S) in
@[expose] def kerQuot (X : Subgroup S.O) (U V : Submodule (ZMod 2) S.Qt)
    (hXU : ∀ x ∈ X, ∀ v ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ U) : Subgroup X where
  carrier := {k | ∀ v ∈ U, ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ V}
  mul_mem' := by
    intro a b ha hb v hv
    rw [Subgroup.coe_mul, coe_mul_apply, show ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v = (((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
          (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) by abel]
    exact add_mem (ha _ (hXU _ b.2 v hv)) (hb v hv)
  one_mem' := fun v _ => by
    rw [show (((1 : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v from rfl, sub_self]
    exact Submodule.zero_mem _
  inv_mem' := by
    intro a ha v hv
    have h := ha _ (hXU _ (inv_mem a.2) v hv)
    rw [apply_inv_apply_O] at h
    have := neg_mem h
    rwa [neg_sub] at this

theorem normal_kerQuot {X : Subgroup S.O} {U V : Submodule (ZMod 2) S.Qt}
    (hXU : ∀ x ∈ X, ∀ v ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ U)
    (hXV : ∀ x ∈ X, ∀ v ∈ V, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V) :
    (kerQuot S X U V hXU).Normal := by
  refine ⟨fun k hk r v hv => ?_⟩
  have h := hXV _ r.2 _ (hk _ (hXU _ (inv_mem r.2) v hv))
  rw [map_sub, apply_inv_apply_O] at h
  have e : (((r * k * r⁻¹ : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) := rfl
  rw [e]
  exact h

section Setup

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hA6 : A6Case H C ht ht1 hVQ)
  (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
include H C ht ht1 hVQ hA6 hR

theorem tri_setup {τ₁ τ₂ : S.O} (h₁ : IsConjCent S t τ₁) (h₂ : IsConjCent S t τ₂)
    (h₃ : IsConjCent S t (t * τ₁ * τ₂)) :
    Vt S g t ⊔ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      Vt S g t ⊔ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      (∀ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ↔
        (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      (∀ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ↔
        ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      (∀ w ∈ Wt S g t, ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) := by
  have htr := hA6.transitive
  have h4 := hA6.finrank_eq
  have hct := commSpace_t_eq H C ht ht1 hVQ
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have i₁ := h₁.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₂ := h₂.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₃ := h₃.inf_eq_bot H C ht ht1 hVQ htr hR
  have f₁ := h₁.finrank_commSpace H C ht ht1 hVQ
  have f₂ := h₂.finrank_commSpace H C ht ht1 hVQ
  have f₃ := h₃.finrank_commSpace H C ht ht1 hVQ
  rw [h4] at f₁ f₂ f₃
  have x₁ := h₁.fix_Vt H C ht ht1 hVQ htr hR
  have l₂ := commSpace_le_Wt_of_fix (h₂.fix_Vt H C ht ht1 hVQ htr hR)
  have l₃ := commSpace_le_Wt_of_fix (h₃.fix_Vt H C ht ht1 hVQ htr hR)
  have htW : ∀ w ∈ Wt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw => by
    rw [← hct.2, mem_fixSpace] at hw
    exact hw
  obtain ⟨e₁, e₂⟩ := sup_eq_sup_of_mul hct.1 htt h4 i₁ i₂ i₃ f₁ f₂ f₃
    (fun v hv => htW v (l₃ hv))
  refine ⟨e₂.trans e₁.symm, e₁.symm, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [fix_iff_mem_orthogonal hw, fix_iff_mem_orthogonal hw, e₁, e₂]
  · rw [fix_iff_mem_orthogonal hw, fix_iff_mem_orthogonal hw, e₁]
  · have hσσ : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) * τ₁ = 1 := by
      have := congrArg Subtype.val (h₁.mul_self H ht)
      exact this
    have hfix₁ : ∀ v ∈ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      have hv' : v ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← e₂.trans e₁.symm]
        exact Submodule.mem_sup_right hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv'
      rw [map_add, x₁ a ha, mem_fixSpace.mp (commSpace_le_fixSpace hσσ hb)]
    exact apply_sub_eq_add htW (fun w hw => h₁.apply_mem_Wt H C ht ht1 hVQ hw) l₂ hfix₁ hw

end Setup

end CFSG.LargeExtraspecial.S9.RB
