module

public import CFSG.GH74.GLS.Stage1.Main.BrBaseTransport
public import CFSG.GH74.GLS.Stage1.Main.BrBaseModel
public import CFSG.GH74.GLS.Stage1.Main.BrModel

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

theorem baseBridge7_thm
    (hII : II4_4_4_center) (h41 : Prop4_1) : BaseBridge7 := by
  intro G _ _ z S q w hcen hT
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, hz'o, hcenS', hz'S', hz'c, hC, hD, hww⟩ :=
    exists_term7_model hodd h5 hK₁ hT7
  have hM := m4_of_std hII hs
  have hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G) :=
    sup_le (sup_le hM.K₁_le hM.K₂_le) hs.sylow.le
  have hcomps := comps_of_std4 hII h41 hs
  have hLB := LBar_eq_imgBar hII h41 hs
  have hSp : IsPGroup 2 ↥S := hs.sylow.isPGroup
  have hSOz : ∀ s ∈ S, s ∈ Oz z → s = 1 := fun s hs' hz =>
    eq_one_of_mem_pgroup_oddCore hSp hs' hz
  obtain ⟨ht, hc₁, hc₂, hne, hu₁, hu₂⟩ :=
    model_swap_data h5 hz'o hz'c hD.Ez_eq hD.E₂_eq hD.sl2 hD.inter_E hD.comm_E hD.t_mem hD.t_ord
  obtain ⟨σ, hσ⟩ := exists_sigma_of_compat hXC (fun H hH => isComponent_map_barOf hII hs hH) hcomps hLB hSp hSOz
    hD.Ez_eq hC hc₁ hc₂ hne
  have hSp' : IsPGroup 2 ↥(S' : Subgroup Gs) := S'.isPGroup'
  have hz'C : (S' : Subgroup Gs) ≤ centralizer ({z'} : Set Gs) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hz'c x hx)
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup Gs) (centralizer ({z'} : Set Gs)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hz'C, hSp', fun hdvd => ?_⟩
    exact S'.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hz'C))
  refine ⟨fun _ => ?_, fun U hUS hU4 hUn => ?_⟩
  · obtain ⟨s, hsσ⟩ := σ.surjective ⟨t', hD.t_mem⟩
    refine ⟨(s : G), s.2, ?_, ?_⟩
    · intro hmem
      have h1 := (hσ s).1 hmem.2
      rw [hsσ] at h1
      have h2 : t' ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') :=
        ⟨h1, Subgroup.mem_sup_left (mem_zpowers t')⟩
      rw [hD.inter, Subgroup.mem_bot] at h2
      have := hD.t_ord
      rw [h2, orderOf_one] at this
      omega
    · have h1 : orderOf s = 2 := by
        rw [← MulEquiv.orderOf_eq σ s, hsσ, Subgroup.orderOf_mk]
        exact hD.t_ord
      rw [← Subgroup.orderOf_coe s] at h1
      exact h1
  ·
    set ρ : ↥S →* Gs := (S' : Subgroup Gs).subtype.comp σ.toMonoidHom with hρ
    have hρinj : Function.Injective ρ := Subtype.coe_injective.comp σ.injective
    set V : Subgroup Gs := (U.subgroupOf S).map ρ with hV
    have hVS : V ≤ S' := by
      rintro _ ⟨x, -, rfl⟩
      exact (σ x).2
    have hUe : IsElementaryAbelian 2 ↥U := hU4.1
    have hUsub : IsElementaryAbelian 2 ↥(U.subgroupOf S) := IsElementaryAbelian.subgroupOf hUS
    have hV4 : IVK.IsFourSubgroup V := by
      refine ⟨IsElementaryAbelian.map ρ, ?_⟩
      rw [hV, Subgroup.card_map_of_injective hρinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
      exact hU4.2
    have hVn : ∀ s ∈ (S' : Subgroup Gs), ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
      intro s hs' v hv
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨s₀, hs₀⟩ := σ.surjective ⟨s, hs'⟩
      have hx' : (x : G) ∈ U := hx
      have hmem : (s₀ : G) * (x : G) * (s₀ : G)⁻¹ ∈ U := hUn (s₀ : G) s₀.2 (x : G) hx'
      refine ⟨s₀ * x * s₀⁻¹, hmem, ?_⟩
      show ((σ (s₀ * x * s₀⁻¹) : ↥S') : Gs) = s * ((σ x : ↥S') : Gs) * s⁻¹
      rw [map_mul, map_mul, map_inv, hs₀]
      rfl
    have hVEz := model_normal_four_le hodd h5 hSp' hsyl' hz'o hz'c hcenS' hD hVS hV4 hVn
    intro u hu
    have hmem : ((σ ⟨u, hUS hu⟩ : ↥S') : Gs) ∈ V := ⟨⟨u, hUS hu⟩, hu, rfl⟩
    exact (hσ ⟨u, hUS hu⟩).2 (hVEz hmem)

end CFSG.GH74.GLS.Stage1.Main
