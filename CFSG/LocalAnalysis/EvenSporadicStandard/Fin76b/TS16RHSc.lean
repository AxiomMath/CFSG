module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHarada

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem sc_step {G : Type} [Group G] {z σ c d : G} {V0 : Subgroup G}
    (hz2 : z * z = 1) (hσ2 : σ * σ = 1) (hzσ : z * σ = σ * z)
    (hV0z : V0 ≤ Subgroup.centralizer ({z} : Set G)) (hV0σ : V0 ≤ Subgroup.centralizer ({σ} : Set G))
    (hzV0 : z ∉ V0 ⊔ Subgroup.zpowers σ)
    (hcV0 : c ∈ V0) (hdV0 : d ∈ V0)
    (hself : ∀ v ∈ V0, v * c = c * v → v * d = d * v → v ∈ Subgroup.closure ({c, d} : Set G)) :
    ∀ s ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers σ ⊔ V0,
      (∀ a ∈ Subgroup.closure ({z, c, d} : Set G), s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers (z * σ)) →
        s ∈ Subgroup.closure ({z, c, d} : Set G) ⊔ Subgroup.zpowers (z * σ) := by
  intro s hs hcomm
  have hu2 : z * σ * (z * σ) = 1 := by
    calc z * σ * (z * σ) = z * (σ * z) * σ := by simp only [mul_assoc]
      _ = z * (z * σ) * σ := by rw [← hzσ]
      _ = z * z * (σ * σ) := by simp only [mul_assoc]
      _ = 1 := by rw [hz2, hσ2, mul_one]
  have huV0 : z * σ ∉ V0 := by
    intro h
    apply hzV0
    have hz : z = z * σ * σ := by rw [mul_assoc, hσ2, mul_one]
    rw [hz]
    exact mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (mem_zpowers σ))
  have hV0u : ∀ x ∈ V0, x ∈ zpowers (z * σ) → x = 1 := by
    intro x hx hxu
    rcases mem_zpowers_sq_eq_one hu2 hxu with h | h
    · exact h
    · rw [h] at hx
      exact absurd hx huV0
  have hVA : V0 ≤ centralizer ((zpowers z ⊔ zpowers σ : Subgroup G) : Set G) := by
    intro v hv
    have hzv : z * v = v * z := Subgroup.mem_centralizer_iff.1 (hV0z hv) z (Set.mem_singleton z)
    have hσv : σ * v = v * σ := Subgroup.mem_centralizer_iff.1 (hV0σ hv) σ (Set.mem_singleton σ)
    have hC : zpowers z ⊔ zpowers σ ≤ centralizer ({v} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzv
      · exact Subgroup.mem_centralizer_singleton_iff.2 hσv
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hC (SetLike.mem_coe.1 hh))
  obtain ⟨p, hp, v, hv, rfl⟩ := exists_mul_of_mem_sup_comm' hVA hs
  have hpV0 : ∀ w ∈ V0, p * w = w * p := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (hVA hw) p (SetLike.mem_coe.2 hp)
  have hstep : ∀ x : G, x ∈ V0 → x ∈ Subgroup.closure ({z, c, d} : Set G) → v * x = x * v := by
    intro x hx hxcl
    have h1 := hcomm x hxcl
    have hw : v * x * v⁻¹ ∈ V0 := mul_mem (mul_mem hv hx) (inv_mem hv)
    have e : p * v * x * (p * v)⁻¹ * x⁻¹ = v * x * v⁻¹ * x⁻¹ := by
      calc p * v * x * (p * v)⁻¹ * x⁻¹ = p * (v * x * v⁻¹) * p⁻¹ * x⁻¹ := by group
        _ = v * x * v⁻¹ * p * p⁻¹ * x⁻¹ := by rw [hpV0 _ hw]
        _ = v * x * v⁻¹ * x⁻¹ := by group
    rw [e] at h1
    have h2 : v * x * v⁻¹ * x⁻¹ = 1 := hV0u _ (mul_mem hw (inv_mem hx)) h1
    have h3 : v * x * v⁻¹ = x := mul_inv_eq_one.1 h2
    calc v * x = v * x * v⁻¹ * v := by group
      _ = x * v := by rw [h3]
  have hc_mem : c ∈ Subgroup.closure ({z, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hd_mem : d ∈ Subgroup.closure ({z, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hvc : v * c = c * v := hstep c hcV0 hc_mem
  have hvd : v * d = d * v := hstep d hdV0 hd_mem
  have hvcl : v ∈ Subgroup.closure ({z, c, d} : Set G) :=
    Subgroup.closure_mono (Set.subset_insert z ({c, d} : Set G)) (hself v hv hvc hvd)
  have hzcl : z ∈ Subgroup.closure ({z, c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hσH : σ ∈ Subgroup.closure ({z, c, d} : Set G) ⊔ zpowers (z * σ) := by
    have e : z * (z * σ) = σ := by rw [← mul_assoc, hz2, one_mul]
    have hm : z * (z * σ) ∈ Subgroup.closure ({z, c, d} : Set G) ⊔ zpowers (z * σ) :=
      mul_mem (Subgroup.mem_sup_left hzcl) (Subgroup.mem_sup_right (mem_zpowers (z * σ)))
    rwa [e] at hm
  have hAH : zpowers z ⊔ zpowers σ ≤ Subgroup.closure ({z, c, d} : Set G) ⊔ zpowers (z * σ) :=
    sup_le (zpowers_le.2 (Subgroup.mem_sup_left hzcl)) (zpowers_le.2 hσH)
  exact mul_mem (hAH hp) (Subgroup.mem_sup_left hvcl)

end CFSG.EvenSporadicStandard.Fin76b
