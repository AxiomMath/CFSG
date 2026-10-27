module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem h518X_of_setup (hS : PlaneSetup z K α)
    (h518 : ∀ (U : Subgroup H) (n : ℕ), U ≤ normalizer (Sec5B517Q8 hS.quad : Set H) →
      (∀ a ∈ U, ∀ b ∈ U,
        (∀ q ∈ Sec5B517Q8 hS.quad,
          a * b * a⁻¹ * b⁻¹ * q * (a * b * a⁻¹ * b⁻¹)⁻¹ * q⁻¹ ∈ zpowers z) ∧
        (∀ q ∈ Sec5B517Q8 hS.quad, a * a * q * (a * a)⁻¹ * q⁻¹ ∈ zpowers z)) →
      ((centralizer (planeV hS.quad α : Set X)).comap α).relIndex U = 2 ^ n → n ≤ 3) :
    ∀ (E : Subgroup X) (n : ℕ), ActsElemAb (planeV hS.quad α) E →
      (centralizer (planeV hS.quad α : Set X)).relIndex E = 2 ^ n → n ≤ 3 := by
  intro E n hE hn
  have hUN : E.comap α ≤ normalizer (Sec5B517Q8 hS.quad : Set H) := fun x hx =>
    (mem_normalizer_planeV_iff hS).mp (hE.le_normalizer hx)
  have key : ∀ g : H, (∀ v ∈ planeV hS.quad α, α g * v * (α g)⁻¹ = v) →
      ∀ q ∈ Sec5B517Q8 hS.quad, g * q * g⁻¹ * q⁻¹ ∈ zpowers z := by
    intro g hg q hq
    rw [← hS.ker, MonoidHom.mem_ker]
    have h := hg (α q) (Subgroup.mem_map_of_mem α hq)
    simp only [map_mul, map_inv]
    rw [h, mul_inv_cancel]
  refine h518 (E.comap α) n hUN ?_ ?_
  · intro a ha b hb
    refine ⟨key (a * b * a⁻¹ * b⁻¹) ?_, key (a * a) ?_⟩
    · intro v hv
      have hc : α b * α a ∈ E := E.mul_mem hb ha
      have hcN : (α b * α a)⁻¹ ∈ normalizer (planeV hS.quad α : Set X) :=
        (normalizer (planeV hS.quad α : Set X)).inv_mem (hE.le_normalizer hc)
      have hv' : (α b * α a)⁻¹ * v * ((α b * α a)⁻¹)⁻¹ ∈ planeV hS.quad α :=
        (Subgroup.mem_set_normalizer_iff.mp hcN v).mp hv
      have h1 := hE.comm (α a) ha (α b) hb _ hv'
      simp only [map_mul, map_inv]
      calc α a * α b * (α a)⁻¹ * (α b)⁻¹ * v * (α a * α b * (α a)⁻¹ * (α b)⁻¹)⁻¹
          = α a * α b * ((α b * α a)⁻¹ * v * ((α b * α a)⁻¹)⁻¹) * (α a * α b)⁻¹ := by group
        _ = α b * α a * ((α b * α a)⁻¹ * v * ((α b * α a)⁻¹)⁻¹) * (α b * α a)⁻¹ := h1
        _ = v := by group
    · intro v hv
      simpa only [map_mul] using hE.sq (α a) ha v hv
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hS.surj]
    exact hn

end CFSG.OddStandard.SmallF3.Omega
