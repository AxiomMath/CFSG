module

public import CFSG.CGT.Stroth77.Section47Harada
public import CFSG.CGT.Stroth77.Section43CoreE

public section

namespace CFSG.CGT.Stroth77

namespace Stroth47

open Stroth42Core

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mul_inv_mem {D U : Subgroup G} {g : G} (hDU : D ≤ U)
    (hg2 : g * g ∈ U) (hconj : ∀ x ∈ U, g⁻¹ * x * g * x⁻¹ ∈ D) :
    g ∈ Subgroup.normalizer (U : Set G) := by
  have hc : ∀ x ∈ U, g⁻¹ * x * g ∈ U := fun x hx => by
    have := U.mul_mem (hDU (hconj x hx)) hx
    rwa [inv_mul_cancel_right] at this
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  refine ⟨fun hy => hc y hy, fun hy => ?_⟩
  have h1 : g * g * (g⁻¹ * y * g) * (g * g)⁻¹ ∈ U := U.mul_mem (U.mul_mem hg2 hy) (U.inv_mem hg2)
  have h2 := hc _ h1
  rwa [show g⁻¹ * (g * g * (g⁻¹ * y * g) * (g * g)⁻¹) * g = y by group] at h2

variable [Finite G]

end Stroth47

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

open Stroth42Core

theorem EAction.mul_self_of_not_mem {h : G} (hE : dD.EAction h) {g : G}
    (hUN : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h ≤
      Subgroup.normalizer (D : Set G))
    (hgU : g ∈ Subgroup.normalizer
      ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h : Subgroup G) : Set G))
    (hg2 : g * g ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h)
    (hconj : ∀ x ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h,
      g⁻¹ * x * g * x⁻¹ ∈ D) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h ⊔ Subgroup.zpowers g,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h →
      ∃ (v : Torus τ.k) (i : Bool), y * y = dD.ofTorus v * dD.d8 i false false * (g * g) := by
  set U := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers h with hU
  intro y hy hyU
  obtain ⟨w, hw, k, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem hgU hg2).mp hy
  cases k
  · exact absurd (by simpa [bpow] using hw) hyU
  simp only [bpow, ↓reduceIte]
  have hd' : g * w * g⁻¹ * w⁻¹ ∈ D := by
    have hx : g * w * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgU w).mp hw
    have := D.inv_mem (hconj _ hx)
    rwa [show (g⁻¹ * (g * w * g⁻¹) * g * (g * w * g⁻¹)⁻¹)⁻¹ = g * w * g⁻¹ * w⁻¹ by group] at this
  obtain ⟨v₁, hv₁⟩ := dD.exists_ofTorus hd'
  have hwd : w * dD.ofTorus v₁ * w⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hUN hw) _).mp (dD.ofTorus_mem v₁)
  obtain ⟨v₂, hv₂⟩ := dD.exists_ofTorus hwd
  have hsq : w * g * (w * g) = w * dD.ofTorus v₁ * w⁻¹ * (w * w) * (g * g) := by
    have : g * w = dD.ofTorus v₁ * w * g := by
      rw [← hv₁]; group
    calc w * g * (w * g) = w * (g * w) * g := by group
      _ = w * (dD.ofTorus v₁ * w * g) * g := by rw [this]
      _ = _ := by group
  rcases hE.mul_self_mem_or w hw with h2 | h2
  · obtain ⟨v₃, hv₃⟩ := dD.exists_ofTorus h2
    refine ⟨v₂ + v₃, false, ?_⟩
    rw [hsq, hv₂, hv₃, dD.d8_fff, mul_one, dD.ofTorus_add]
  · obtain ⟨v₃, hv₃⟩ := dD.exists_ofTorus h2
    refine ⟨v₂ + v₃, true, ?_⟩
    have hww : w * w = dD.ofTorus v₃ * dD.uv := by
      rw [← hv₃, mul_assoc, dD.uv_sq, mul_one]
    rw [hsq, hv₂, hww, dD.d8_tff, dD.ofTorus_add]
    group

end StrothWeakTypeData

end CFSG.CGT.Stroth77
