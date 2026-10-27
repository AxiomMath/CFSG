module

public import CFSG.LargeExtraspecial.S11ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_apply_cl (H : Hyp4 S g) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have h : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [H.fixSub_eq]
    exact Submodule.mem_span_singleton_self _
  rw [mem_fixSub] at h
  exact h s hs

theorem Lbar_sub_mem_clSub (H : Hyp4 S g) (C : Cons311 S g) {s : S.O} (hs : s ∈ S.Lbar g)
    {x : S.Qt} (hx : polar S.q (S.cl (g * S.z * g⁻¹)) x = 0) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨x₀, hx₀Q, rfl⟩ := S.exists_cl x
  rw [S.polar_cl_eq_zero_iff H.conj_mem hx₀Q] at hx
  exact C.comm_le x₀ (mem_inf.mpr ⟨hx₀Q, mem_centralizer_singleton_iff.mpr hx.symm⟩) s hs

theorem Hyp.not_isTypeA_of_mem_Lbar (hy : Hyp S g) {s : S.O} (hs : s ∈ S.Lbar g)
    (hs1 : s ≠ 1) : ¬ IsTypeA S.q (s : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨x, hx, rfl⟩ := (S4.mem_Lbar S).mp hs
  exact hy.noA2' x ((L0_le_La S g) hx) fun h => hs1 ((S.ρ_eq_one_iff x).mpr h)

theorem finrank_inf_fixSpace_add_one (H : Hyp4 S g) (C : Cons311 S g) {s : S.O}
    (hs : s ∈ S.Lbar g) (hs1 : s ≠ 1) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) + 1 =
      S.width := by
  have hdim := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have h1 := S2.finrank_map_sub_one_add (s : S.Qt ≃ₗ[ZMod 2] S.Qt) P
  have hmap : P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Lbar_apply_sub_mem_span' H.conj_mem hv hs
  have h2 := Submodule.finrank_mono hmap
  have h3 := finrank_span_singleton_le_one (S.cl (g * S.z * g⁻¹))
  have hne : P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≠ ⊥ := by
    intro h0
    apply hs1
    refine C.faithful s hs fun v hv => ?_
    have : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
        P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have h4 : finrank (ZMod 2) (P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) ≠ 0 :=
    fun h => hne (Submodule.finrank_eq_zero.mp h)
  omega

theorem finrank_inf_fixSpace_inf_le (H : Hyp4 S g) (C : Cons311 S g) {s₁ s₂ : S.O}
    (hs₁ : s₁ ∈ S.Lbar g) (hs₂ : s₂ ∈ S.Lbar g) (h1 : s₁ ≠ 1) (h2 : s₂ ≠ 1) (h12 : s₁ ≠ s₂) :
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt))) + 2 ≤ S.width := by
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set F₁ := P ⊓ fixSpace (s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hF₁
  set F₂ := P ⊓ fixSpace (s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hF₂
  have d₁ := finrank_inf_fixSpace_add_one H C hs₁ h1
  have d₂ := finrank_inf_fixSpace_add_one H C hs₂ h2
  by_contra hcon
  push Not at hcon
  have e₁ : F₁ ⊓ F₂ = F₁ :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [← hF₁] at d₁; omega)
  have e₂ : F₁ ⊓ F₂ = F₂ :=
    Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [← hF₂] at d₂; omega)
  have hF : F₁ = F₂ := e₁.symm.trans e₂
  have ha₁ := Lbar_apply_cl H hs₁
  have hcl : ∀ (s : S.O), s ∈ S.Lbar g → ∀ p ∈ P, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) p ≠ p →
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p + S.cl (g * S.z * g⁻¹) := by
    intro s hs p hp hsp
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Lbar_apply_sub_mem_span' H.conj_mem hp hs)
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at hc
      exact absurd hc hsp
    · rw [one_smul] at hc
      rw [hc]
      abel
  have hfix : ∀ p ∈ P, ((s₁ * s₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
    intro p hp
    rw [coe_mul_apply]
    by_cases hp₁ : (s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p
    · have hp₂ : p ∈ F₂ := hF ▸ (⟨hp, mem_fixSpace.mpr hp₁⟩ : p ∈ F₁)
      rw [mem_fixSpace.mp hp₂.2, hp₁]
    · have hp₂ : (s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ≠ p := fun h => by
        have hp₂ : p ∈ F₁ := hF ▸ (⟨hp, mem_fixSpace.mpr h⟩ : p ∈ F₂)
        exact hp₁ (mem_fixSpace.mp hp₂.2)
      rw [hcl s₂ hs₂ p hp hp₂, map_add, hcl s₁ hs₁ p hp hp₁, ha₁, add_assoc, vec_add_self,
        add_zero]
  have h := C.faithful _ (mul_mem hs₁ hs₂) hfix
  apply h12
  calc s₁ = s₁ * (s₂ * s₂) := by rw [mul_self_of_mem_Lbar S H.conj_mem hs₂, mul_one]
    _ = (s₁ * s₂) * s₂ := by group
    _ = s₂ := by rw [h, one_mul]

end CFSG.LargeExtraspecial.S11
