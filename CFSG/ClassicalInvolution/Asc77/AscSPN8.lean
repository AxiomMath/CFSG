module

public import CFSG.ClassicalInvolution.Asc77.AscT7ND
public import CFSG.ClassicalInvolution.Asc77.AscT7NE
public import CFSG.ClassicalInvolution.Asc77.AscT7NJ
public import CFSG.ClassicalInvolution.Asc77.AscT7RG

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace SPN

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}


theorem centralizer_z_le_sigmaNorm (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({z} : Set G) ≤ sigmaNorm Ω K := fun g hg => by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK]
  exact h.conjSub_mem_dComp_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hg)

theorem centralizer_t_le_sigmaNorm (h : Hyp21 p f Ω K K' z u J t W) :
    Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K := fun g hg => by
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJd : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hJK
  have hgt : g * t * g⁻¹ = t := by
    have := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    calc g * t * g⁻¹ = (t * g) * g⁻¹ := by rw [this]
      _ = t := by group
  have hJgt : IsUniqueInvolution (conjSub g J) t := by
    have := h.ht.conj g
    rwa [hgt] at this
  have h1 : conjSub g J ∈ dComp Ω J :=
    T7A.mem_dComp_of_mem_kPerp (mem_kPerp_of_twin hΩ (hΩ.conjInvariant g J hJΩ) hJΩ hJgt h.ht)
  have h2 : conjSub g J ∈ dComp Ω K := by
    rwa [T8.dComp_eq_of_mem hK hJd] at h1
  exact T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hJd h2

theorem oddCore_rLayer_le_sigmaNorm (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    oddCoreOf (rLayer Ω u) ≤ sigmaNorm Ω K := fun _ hn =>
  centralizer_z_le_sigmaNorm h (Subgroup.mem_centralizer_singleton_iff.mpr
    (h.oddCore_centralizer_u_comm hα (h.oddCore_rLayer_u_le hn)))

theorem exists_r_not_sigmaNorm (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ∃ r ∈ rLayer Ω u, r ∉ sigmaNorm Ω K := by
  classical
  have hst := h.std.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hst.aEmpty⟩
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have c : Ctx p f Ω W := MuTab.muTabCtx hP h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hK hz h.hzW
  obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hK'Ω hzK' h.hzW
  obtain ⟨ρ_L, hL1', hL2'⟩ := T7N.exists_noncomm_rep c hnc ρ₁
  have hL1 : ρ_L.K ≠ K := by rw [← hρ₁]; exact hL1'
  have hL2 : ρ_L.K ∉ omegaNbr Ω K := by rw [← hρ₁]; exact hL2'
  have hK'K : K' ∈ omegaNbr Ω K := T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have hLK' : ρ_L.K ≠ K' := fun e => hL2 (e ▸ hK'K)
  obtain ⟨z_L, hzL⟩ := hΩ.exists_uniqueInvolution hp hq ρ_L.hK
  obtain ⟨u₀, -, hu₀mem, hu₀sq, hu₀1, hu₀z, hRL, -⟩ := T7N.exists_adapted_involution c
    ρ₁ ρ₂ ρ_L (hρ₁ ▸ hz) (hρ₂ ▸ hzK') hzL (by rw [hρ₁, hρ₂]; exact h.std.hne.symm)
    (by rw [hρ₁]; exact hL1) (by rw [hρ₂]; exact hLK') (by rw [hρ₁]; exact hL2)
  rw [hρ₁, hρ₂] at hu₀mem
  have hrLS : ρ_L.r ∉ sigmaNorm Ω K := T7N.Hyp21.r_not_mem_sigmaNorm h hne ρ₁ ρ_L hρ₁ hL1 hL2
  obtain ⟨x, hx, hxu⟩ := T7N.exists_conj_of_involution_twin hp hΩ hK hK'Ω h.std.hne hz hzK'
    hu₀mem hu₀1 hu₀z hu₀sq h.hu h.hu1 h.huz h.hu2
  have hxN : x ∈ sigmaNorm Ω K :=
    T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK
      (T7N.sup_le_normalizer_of_twin hΩ hK hK'Ω h.std.hne hz hzK' hx)
  have hR1 : conjSub x ρ_L.R ∈ RSet Ω := RSet.conj hΩ.conjInvariant ρ_L.hR.1 x
  have hR2 : conjSub x ρ_L.R ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyu : y * u₀ = u₀ * y := Subgroup.mem_centralizer_singleton_iff.mp (hRL hy)
    show (x * y * x⁻¹) * u = u * (x * y * x⁻¹)
    rw [← hxu]
    calc x * y * x⁻¹ * (x * u₀ * x⁻¹) = x * (y * u₀) * x⁻¹ := by group
      _ = x * (u₀ * y) * x⁻¹ := by rw [hyu]
      _ = x * u₀ * x⁻¹ * (x * y * x⁻¹) := by group
  refine ⟨x * ρ_L.r * x⁻¹, ?_, fun hmem => hrLS ?_⟩
  · have hle : conjSub x ρ_L.R ≤ rLayer Ω u := le_iSup₂_of_le _ hR1 (le_iSup_of_le hR2 le_rfl)
    exact hle (conj_mem_conjSub ρ_L.hr)
  · have := (sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).inv_mem hxN) hmem)
      hxN
    simpa [mul_assoc] using this

end SPN

end CFSG.ClassicalInvolution.Asc77
