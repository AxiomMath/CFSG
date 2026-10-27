module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qG1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qG2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_lemmaF
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) (hG : Sec4Glob G)
    (hH : ∀ u ∈ ctxO t tau x₁ x₂, u * u = 1 → u * t = t * u) : False := by
  obtain ⟨v, hvU, hv1, hv2, hv2U⟩ := w4q_exists_v hc.U_sylow.2.1 (w4q_idx_U hc hG)
  have hFO := w4q_F_le_O hc hH hv1 hv2
  obtain ⟨hFelem, hFcard⟩ := w4q_F_elem hc v
  have hFU := w4q_F_le_U hc hv1
  have hSyl : IsSylowIn 2 S (invCent t) := ⟨hc.le_invCent, hc.isPGroup, hc.relIndex_odd⟩
  have hFS : cj v (ctxX t tau x₁ x₂) ≤ S := by
    intro f hf
    have hft : f * t = t * f := hH f (hFO hf) (hFelem.mul_self_eq_one hf)
    rw [← w4q_S_eq hc]
    exact ⟨hFU hf, Subgroup.mem_centralizer_singleton_iff.mpr hft⟩
  have htF : t ∈ cj v (ctxX t tau x₁ x₂) :=
    (hc.l47.1 (cj v (ctxX t tau x₁ x₂)) ⟨hFS, hFelem, hFcard⟩).2.1
      (Subgroup.subset_closure (by simp))
  have h1 : v⁻¹ * t * v⁻¹⁻¹ ∈ ctxX t tau x₁ x₂ := by
    rw [inv_inv]
    exact mem_cj.mp htF
  obtain ⟨w, hw, hwe⟩ := Set.mem_smul_set.mp (hc.tG_X v⁻¹ h1)
  rw [smul_eq_mul, inv_inv] at hwe
  obtain ⟨u, hu, hut⟩ := w4q_tU hc hw
  have hct : (v * u) * t = t * (v * u) := by
    have e1 : v * (u * t * u⁻¹) * v⁻¹ = t := by rw [hut, hwe]; group
    calc (v * u) * t = (v * (u * t * u⁻¹) * v⁻¹) * (v * u) := by group
      _ = t * (v * u) := by rw [e1]
  have hct' : (v * u)⁻¹ * t = t * (v * u)⁻¹ :=
    (Commute.inv_left (show Commute (v * u) t from hct)).eq
  have hcU : v * u ∉ ctxU t tau x₁ x₂ lam := by
    intro h
    apply hvU
    have h2 := mul_mem h (inv_mem hu)
    rwa [mul_inv_cancel_right] at h2
  have hcN : ∀ s ∈ ctxU t tau x₁ x₂ lam, (v * u) * s * (v * u)⁻¹ ∈ ctxU t tau x₁ x₂ lam := by
    intro s hs
    have h2 := hv1 _ (mul_mem (mul_mem hu hs) (inv_mem hu))
    have e : (v * u) * s * (v * u)⁻¹ = v * (u * s * u⁻¹) * v⁻¹ := by group
    rwa [← e] at h2
  have hc2U : (v * u) ^ 2 ∈ ctxU t tau x₁ x₂ lam := by
    have e : (v * u) ^ 2 = v ^ 2 * (v⁻¹ * u * v) * u := by
      simp only [pow_two]
      group
    rw [e]
    exact mul_mem (mul_mem hv2U (hv2 u hu)) hu
  have hc2t : (v * u) ^ 2 * t = t * (v * u) ^ 2 :=
    (Commute.pow_left (show Commute (v * u) t from hct) 2).eq
  have hc2S : (v * u) ^ 2 ∈ S := by
    rw [← w4q_S_eq hc]
    exact ⟨hc2U, Subgroup.mem_centralizer_singleton_iff.mpr hc2t⟩
  have hcNS : ∀ s ∈ S, (v * u) * s * (v * u)⁻¹ ∈ S := by
    intro s hs
    have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_invCent hs)
    rw [← w4q_S_eq hc]
    refine ⟨hcN s (hc.S_le_U hs), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (v * u) * s * (v * u)⁻¹ * t = (v * u) * s * ((v * u)⁻¹ * t) := by group
      _ = (v * u) * s * (t * (v * u)⁻¹) := by rw [hct']
      _ = (v * u) * (s * t) * (v * u)⁻¹ := by group
      _ = (v * u) * (t * s) * (v * u)⁻¹ := by rw [hst]
      _ = ((v * u) * t) * s * (v * u)⁻¹ := by group
      _ = (t * (v * u)) * s * (v * u)⁻¹ := by rw [hct]
      _ = t * ((v * u) * s * (v * u)⁻¹) := by group
  have hcK : v * u ∈ invCent t := Subgroup.mem_centralizer_singleton_iff.mpr hct
  exact hcU (hc.S_le_U (w4q_mem_of_normalizes hSyl hcK hcNS hc2S))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
