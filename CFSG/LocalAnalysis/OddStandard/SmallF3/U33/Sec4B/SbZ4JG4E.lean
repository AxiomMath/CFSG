module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G}

theorem z4j_sylow_lift {Vg V : Subgroup G} (hVg2 : IsPGroup 2 Vg)
    (hbound : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R →
      R ≤ centralizer ({g * t * g⁻¹} : Set G) → Nat.card R ≤ 128)
    (hchar : ∀ z ∈ normalizer (Vg : Set G), ∀ v ∈ V, z * v * z⁻¹ ∈ V)
    (hs : ∃ s ∈ Vg, s * s = 1 ∧ s ∉ centralizer (V : Set G) ∧ (∃ g : G, s = g * t * g⁻¹) ∧
      (∀ x ∈ Vg, x * x = 1 → x ∉ centralizer (V : Set G) → (∃ g : G, x = g * t * g⁻¹) →
        ∃ w ∈ Vg, x = w * s * w⁻¹) ∧ Nat.card ↥(Vg ⊓ centralizer ({s} : Set G)) = 128) :
    ¬ 2 ∣ Vg.index := by
  obtain ⟨s, hsVg, hs2, hsV, ⟨g₀, hg₀⟩, hfus, hcardV⟩ := hs
  refine z4j_sylow_of_fusion (D := centralizer (V : Set G)) hVg2 hsVg hs2 hsV ?_ ?_ ?_
  · intro z hz x hx hxD hzx
    apply hxD
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : z * v * z⁻¹ ∈ V := hchar z hz v hv
    have h2 := (Subgroup.mem_centralizer_iff.mp hzx) (z * v * z⁻¹) h1
    have h3 : z * (v * x) * z⁻¹ = z * (x * v) * z⁻¹ := by
      calc z * (v * x) * z⁻¹ = z * v * z⁻¹ * (z * x * z⁻¹) := by group
        _ = z * x * z⁻¹ * (z * v * z⁻¹) := h2
        _ = z * (x * v) * z⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  · intro x hxP hx2 hxD ⟨g, hg⟩
    exact hfus x hxP hx2 hxD ⟨g * g₀, by rw [hg, hg₀]; group⟩
  · intro R hR hRc
    rw [hcardV]
    exact hbound g₀ R hR (by rw [← hg₀]; exact hRc)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
