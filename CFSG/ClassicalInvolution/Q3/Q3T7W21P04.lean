module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21N08
public import CFSG.ClassicalInvolution.Q3.Q3T7W21S01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}

theorem Hyp21.centralizer_z_le_sigmaNorm (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaNorm Ω K := fun g hg => by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK]
  exact h.conjSub_mem_dComp_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hg)

theorem Hyp21.centralizer_t_le_sigmaNorm (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K := fun g hg => by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJd : J ∈ dComp Ω K := T7A.mem_dComp_of_mem_omegaNbr hJK
  have hgt : g * t * g⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * t * g⁻¹ = (t * g) * g⁻¹ := by rw [this]
      _ = t := by group
  have hJgt : IsUniqueInvolution (conjSub g J) t := by
    have := h.ht.conj g
    rwa [hgt] at this
  have h1 : conjSub g J ∈ dComp Ω J :=
    T7A.mem_dComp_of_mem_kPerp
      (Q3T7M.mem_kPerp_of_twin (Q3T7.modU_toGen3 hΩ) (hΩ.conjInvariant g J hJΩ) hJΩ hJgt h.ht)
  have h2 : conjSub g J ∈ dComp Ω K := by
    rwa [T8.dComp_eq_of_mem hK hJd] at h1
  exact T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hJd h2

theorem Hyp21.oddCore_exactLayer_u_le_sigmaNorm (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    oddCoreOf (ExactLayer.exactLayer Ω u) ≤ sigmaNorm Ω K := fun _ hn =>
  h.centralizer_z_le_sigmaNorm (Subgroup.mem_centralizer_singleton_iff.mpr
    (h.oddCore_centralizer_u_comm hα
      (oddCoreOf_exactLayer_le (h.std.stand.modU).conjInvariant u hn)))

variable [IsSimpleGroup G]

theorem Hyp21.exists_r_not_sigmaNorm (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ r ∈ ExactLayer.exactLayer Ω u, r ∉ sigmaNorm Ω K := by
  classical
  have hst := h.std.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hst.cls hK hz h.hzW
  obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hst.cls hK'Ω hzK' h.hzW
  obtain ⟨ρ_L, hL1', hL2'⟩ := T7N.exists_noncomm_rep c hnc ρ₁
  have hL1 : ρ_L.K ≠ K := by rw [← hρ₁]; exact hL1'
  have hL2 : ρ_L.K ∉ omegaNbr Ω K := by rw [← hρ₁]; exact hL2'
  have hK'K : K' ∈ omegaNbr Ω K :=
    Q3CL.T3.twin_mem_omegaNbr hst.hyp hK hK'Ω h.std.hne hz hzK'
  have hLK' : ρ_L.K ≠ K' := fun e => hL2 (e ▸ hK'K)
  obtain ⟨z_L, hzL⟩ := hΩ.exists_uniqueInvolution ρ_L.hK
  obtain ⟨u₀, -, hu₀mem, hu₀sq, hu₀1, hu₀z, hRL, -⟩ := T7N.exists_adapted_involution c
    ρ₁ ρ₂ ρ_L (hρ₁ ▸ hz) (hρ₂ ▸ hzK') hzL (by rw [hρ₁, hρ₂]; exact h.std.hne.symm)
    (by rw [hρ₁]; exact hL1) (by rw [hρ₂]; exact hLK') (by rw [hρ₁]; exact hL2)
  rw [hρ₁, hρ₂] at hu₀mem
  have hrLS : ρ_L.r ∉ sigmaNorm Ω K := Hyp21.r_not_mem_sigmaNorm h hne ρ₁ ρ_L hρ₁ hL1 hL2
  obtain ⟨x, hx, hxu⟩ := T7N.exists_conj_of_involution_twin hΩ hK hK'Ω h.std.hne hz hzK'
    hu₀mem hu₀1 hu₀z hu₀sq h.hu h.hu1 h.huz h.hu2
  have hEN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (hΩ.le_normalizer_of_twin hK'Ω hK h.std.hne hzK' hz)
  have hxN : x ∈ sigmaNorm Ω K := T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK (hEN hx)
  have hR2 : conjSub x ρ_L.R ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyu : y * u₀ = u₀ * y := Subgroup.mem_centralizer_singleton_iff.mp (hRL hy)
    show (x * y * x⁻¹) * u = u * (x * y * x⁻¹)
    rw [← hxu]
    calc x * y * x⁻¹ * (x * u₀ * x⁻¹) = x * (y * u₀) * x⁻¹ := by group
      _ = x * (u₀ * y) * x⁻¹ := by rw [hyu]
      _ = x * u₀ * x⁻¹ * (x * y * x⁻¹) := by group
  have hLSyl : IsSylow2In (conjSub x ρ_L.R) (conjSub x ρ_L.K) := ρ_L.hRK.conj x
  have hLΩ : conjSub x ρ_L.K ∈ Ω := hΩ.conjInvariant x ρ_L.K ρ_L.hK
  have hY : conjSub x ρ_L.R ≤ ExactLayer.exactLayer Ω u :=
    T7N.le_exactLayer_of_sylow hΩ h.hu2 hLΩ hLSyl hR2
  refine ⟨x * ρ_L.r * x⁻¹, hY (conj_mem_conjSub ρ_L.hr), fun hmem => hrLS ?_⟩
  have := (sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).inv_mem hxN) hmem)
    hxN
  simpa [mul_assoc] using this

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
