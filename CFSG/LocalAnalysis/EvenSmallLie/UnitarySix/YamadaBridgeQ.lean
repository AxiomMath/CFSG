module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDInter
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.LemmaQ

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

structure ConfigPart {G : Type*} [Group G] (Y D X E : Subgroup G) (t : G) : Prop where
  t_sq : t * t = 1
  D_le : D ≤ Y
  D_comm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a
  D_sq : ∀ d ∈ D, d * d = 1
  t_normD : t ∈ normalizer (D : Set G)
  D_conj : ∀ d ∈ D, d * t = t * d → ∃ d' ∈ D, d'⁻¹ * t * d' = d * t
  normD_of_norm : ∀ y ∈ Y, y ∈ normalizer (LemmaQ.centInvSup D t : Set G) →
    y ∈ normalizer (D : Set G)
  E_le : E ≤ Y
  E_t : ∀ u ∈ E, ∃ x ∈ X, ∃ d ∈ D, u⁻¹ * t * u = x * d * t

namespace Hyp

variable {G : Type*} [Group G] {d : Data G} (h : Hyp d) (hB : HypB d)
include h hB

theorem configPart [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hCe : ∀ a ∈ d.A₁, a * d.e = d.e * a → ∃ x ∈ d.X₁, ∃ b ∈ d.X₈ ⊔ zpowers d.z, a = x * b) :
    ConfigPart (centralizer ({d.e} : Set G)) d.D₄ d.X₁ (d.D₁ ⊓ centralizer ({d.e} : Set G))
      d.t := by
  have hcent : LemmaQ.centInvSup d.D₄ d.t = d.withT d.A₄ := by
    rw [LemmaQ.centInvSup, Data.withT, ← h.D₄_inf_H]
    rfl
  have heC : ∀ {x : G}, x ∈ centralizer ({d.e} : Set G) → x * d.e = d.e * x := fun hx =>
    (mem_centralizer_singleton_iff.mp hx)
  refine
    { t_sq := h.t_sq
      D_le := h.D₄_le_D.trans D_le_cent_e
      D_comm := fun a ha b hb => h.D₄_comm ha hb
      D_sq := fun y hy => h.D₄_sq hB hV hy
      t_normD := h.t_mem_normalizer_D₄
      D_conj := fun y hy hyt => by
        have hyA : y ∈ d.A₄ := h.D₄_inf_H ▸
          (mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyt⟩ : y ∈ d.D₄ ⊓ d.H)
        exact h.exists_D₄_conj hyA
      normD_of_norm := fun y _ hy => by
        rw [hcent] at hy
        exact h.X₄_le_normalizer_D₄ hy
      E_le := inf_le_right
      E_t := fun u hu => ?_ }
  obtain ⟨hu1, hue⟩ := mem_inf.mp hu
  have hθ := h.crossed_D₁ hB hV hu1
  obtain ⟨a, ha, v, hv, hav⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hθ
  have hte : d.t ∈ centralizer ({d.e} : Set G) :=
    mem_centralizer_singleton_iff.mpr h.e_comm_t.symm
  have hθe : d.theta u ∈ centralizer ({d.e} : Set G) := by
    rw [Data.theta]
    exact mul_mem (mul_mem (mul_mem (inv_mem hue) hte) hue) hte
  have hve : v ∈ centralizer ({d.e} : Set G) := D_le_cent_e (h.D₄_le_D (V₁_le_D₄ hv))
  have hae : a * d.e = d.e * a := by
    have : a = d.theta u * v⁻¹ := by rw [← hav]; group
    rw [this]
    exact heC (mul_mem hθe (inv_mem hve))
  obtain ⟨x, hx, b, hb, rfl⟩ := hCe a ha hae
  refine ⟨x, hx, b * v, mul_mem (h.Z₂S_le_V₂.trans h.V₂_le_D₄ hb) (V₁_le_D₄ hv), ?_⟩
  have e1 : u⁻¹ * d.t * u = d.theta u * d.t := by
    rw [Data.theta, mul_assoc _ d.t d.t, h.t_sq, mul_one]
  rw [e1, ← hav]
  group

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
