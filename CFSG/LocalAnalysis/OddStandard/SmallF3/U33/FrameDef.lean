module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

@[expose] def autFixed {K : Type*} [Group K] (α : MulAut K) : Subgroup K where
  carrier := {k | α k = k}
  one_mem' := map_one α
  mul_mem' {a b} ha hb := by
    change α a = a at ha
    change α b = b at hb
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change α a = a at ha
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

section Generic

variable {K K' : Type*} [Group K] [Group K']

theorem WreathRel.of_injective (f : K →* K') (hf : Function.Injective f) {x₁ x₂ lam : K}
    (h : WreathRel (f x₁) (f x₂) (f lam)) : WreathRel x₁ x₂ lam := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective f hf x₁).symm.trans h.ord_x₁
  · exact (orderOf_injective f hf x₂).symm.trans h.ord_x₂
  · exact hf (by simpa only [map_mul] using h.comm)
  · rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have h1 : f g ∈ zpowers (f x₁) := by
      rw [← MonoidHom.map_zpowers f x₁]
      exact Subgroup.mem_map_of_mem f hg.1
    have h2 : f g ∈ zpowers (f x₂) := by
      rw [← MonoidHom.map_zpowers f x₂]
      exact Subgroup.mem_map_of_mem f hg.2
    have hbot : f g ∈ (⊥ : Subgroup K') := by
      rw [← h.inf_eq_bot]
      exact ⟨h1, h2⟩
    have hg1 : f g = 1 := Subgroup.mem_bot.mp hbot
    exact hf (by rw [hg1, map_one])
  · exact (orderOf_injective f hf lam).symm.trans h.ord_lam
  · exact hf (by simpa only [map_mul, map_inv] using h.conj_x₁)

theorem WreathRel.map' (f : K →* K') (hf : Function.Injective f) {x₁ x₂ lam : K}
    (h : WreathRel x₁ x₂ lam) : WreathRel (f x₁) (f x₂) (f lam) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective f hf x₁).trans h.ord_x₁
  · exact (orderOf_injective f hf x₂).trans h.ord_x₂
  · rw [← map_mul, ← map_mul, h.comm]
  · rw [← MonoidHom.map_zpowers f x₁, ← MonoidHom.map_zpowers f x₂,
      ← Subgroup.map_inf (zpowers x₁) (zpowers x₂) f hf, h.inf_eq_bot, Subgroup.map_bot]
  · exact (orderOf_injective f hf lam).trans h.ord_lam
  · rw [← map_mul, ← map_inv, ← map_mul, h.conj_x₁]

end Generic

section Frame

variable {K : Type*} [Group K]

structure U33Frame (x₁ x₂ lam rho : K) (α : MulAut K) : Prop where
  wreath : WreathRel x₁ x₂ lam
  ord_rho : orderOf rho = 3
  rho_x₁ : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂
  rho_x₂ : rho * x₂ * rho⁻¹ = x₁⁻¹
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹
  cent_rho : ∀ w ∈ baseGrp x₁ x₂, rho * w = w * rho → w = 1
  alpha_sq : α * α = 1
  alpha_x₁ : α x₁ = x₁⁻¹
  alpha_x₂ : α x₂ = x₂⁻¹
  alpha_lam : α lam = lam
  alpha_rho : α rho = rho
  alpha_outer : ∀ k : K, α ≠ MulAut.conj k

theorem U33Frame.map {x₁ x₂ lam rho : K} {α : MulAut K} (h : U33Frame x₁ x₂ lam rho α)
    (γ : MulAut K) : U33Frame (γ x₁) (γ x₂) (γ lam) (γ rho) (γ * α * γ⁻¹) :=
  { wreath := WreathRel.map' γ.toMonoidHom γ.injective h.wreath
    ord_rho := (MulEquiv.orderOf_eq γ rho).trans h.ord_rho
    rho_x₁ := by simpa only [map_mul, map_inv] using congrArg (γ : K → K) h.rho_x₁
    rho_x₂ := by simpa only [map_mul, map_inv] using congrArg (γ : K → K) h.rho_x₂
    lam_rho := by simpa only [map_mul, map_inv] using congrArg (γ : K → K) h.lam_rho
    cent_rho := by
      intro w hw hcomm
      have hmap : (baseGrp x₁ x₂).map γ.toMonoidHom = baseGrp (γ x₁) (γ x₂) := by
        simp only [baseGrp, MonoidHom.map_closure, Set.image_pair, MulEquiv.coe_toMonoidHom]
      rw [← hmap] at hw
      have hw' : γ.symm w ∈ baseGrp x₁ x₂ := (Subgroup.mem_map_equiv (f := γ)).mp hw
      have hcomm' : rho * γ.symm w = γ.symm w * rho := by
        apply γ.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hcomm
      have hw1 : γ.symm w = 1 := h.cent_rho (γ.symm w) hw' hcomm'
      rw [← MulEquiv.apply_symm_apply γ w, hw1, map_one]
    alpha_sq := by
      rw [show γ * α * γ⁻¹ * (γ * α * γ⁻¹) = γ * (α * α) * γ⁻¹ by group, h.alpha_sq]
      group
    alpha_x₁ := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h.alpha_x₁,
        map_inv]
    alpha_x₂ := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h.alpha_x₂,
        map_inv]
    alpha_lam := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h.alpha_lam]
    alpha_rho := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h.alpha_rho]
    alpha_outer := by
      intro k hk
      apply h.alpha_outer (γ⁻¹ k)
      have h1 : α = γ⁻¹ * MulAut.conj k * γ := by
        rw [← hk]; group
      have h2 : γ⁻¹ * MulAut.conj k * γ = MulAut.conj (γ⁻¹ k) := by
        ext x
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.symm_apply_apply]
      exact h1.trans h2 }

end Frame

end CFSG.OddStandard.SmallF3.HarrisU33
