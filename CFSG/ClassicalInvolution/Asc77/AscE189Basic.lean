module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Basic

variable {G : Type} [Group G]

variable {Ω : Set (Subgroup G)} {K H : Subgroup G}

theorem mem_twinSet_self {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) :
    K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩

theorem e189_commute_of_mem {K : Subgroup G} {z w : G} (hz : IsUniqueInvolution K z)
    (hw : w ∈ K) : z * w = w * z := by
  have h1 : w * z * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hw hz.mem) (K.inv_mem hw)
  have h2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    have : z = w⁻¹ * (w * z * w⁻¹) * w := by group
    rw [this, h]
    group
  · calc z * w = (w * z * w⁻¹) * w := by rw [h]
      _ = w * z := by group

theorem smul_mk_eq_iff {a : G} {H : Subgroup G} (g : G) :
    a • ((g : G) : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * a * g ∈ H := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  have e : (a * g)⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
  rw [e, inv_mem_iff]

theorem fixesUniqueCoset_conj {a : G} {H : Subgroup G} (h : FixesUniqueCoset a H) (g : G) :
    FixesUniqueCoset (g * a * g⁻¹) H := by
  obtain ⟨c, hc, hu⟩ := h
  refine ⟨g • c, ?_, fun d hd => ?_⟩
  · have e : (g * a * g⁻¹) • (g • c) = g • (a • c) := by
      rw [← mul_smul, ← mul_smul, show g * a * g⁻¹ * g = g * a by group]
    show (g * a * g⁻¹) • (g • c) = g • c
    rw [e, hc]
  · have : a • (g⁻¹ • d) = g⁻¹ • d := by
      have e : a • (g⁻¹ • d) = g⁻¹ • ((g * a * g⁻¹) • d) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      rw [e, show (g * a * g⁻¹) • d = d from hd]
    have := hu _ this
    rw [← this, smul_inv_smul]

theorem fixesUniqueCoset_of_centralizer_le {a : G} {H : Subgroup G}
    (hcent : Subgroup.centralizer ({a} : Set G) ≤ H)
    (h7 : ∀ g : G, g * a * g⁻¹ ∈ H → ∃ k ∈ H, k * a * k⁻¹ = g * a * g⁻¹) :
    FixesUniqueCoset a H := by
  have haH : a ∈ H := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine ⟨(1 : G), ?_, ?_⟩
  · exact (smul_mk_eq_iff (a := a) (H := H) 1).mpr (by simpa using haH)
  · intro c' hc'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c'
    have hg : g⁻¹ * a * g ∈ H := (smul_mk_eq_iff g).mp hc'
    obtain ⟨k, hk, hka⟩ := h7 g⁻¹ (by simpa using hg)
    have hgk : g * k ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : k * a * k⁻¹ = g⁻¹ * a * g := by simpa using hka
      calc (g * k) * a = (g * (k * a * k⁻¹)) * k := by group
        _ = a * (g * k) := by rw [h3]; group
    have : g ∈ H := by
      have h4 : g * k * k⁻¹ ∈ H := H.mul_mem (hcent hgk) (H.inv_mem hk)
      simpa using h4
    exact (QuotientGroup.eq.mpr (by simpa using H.inv_mem this)).symm

theorem mul_involution_of_commute {z t : G} (hz : z * z = 1) (ht : t * t = 1)
    (hzt : z * t = t * z) : (z * t) * (z * t) = 1 := by
  calc (z * t) * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [hzt]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [hz, ht, one_mul]

end Basic

end CFSG.ClassicalInvolution.Asc77
