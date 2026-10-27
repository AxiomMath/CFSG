module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedTrans
public import CFSG.GH74.GLS.Stage1.Main.BrFusedModel
public import CFSG.GH74.GLS.Stage1.Main.BrFusedStmt

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

namespace CFSG.GH74.GLS.Stage1.Main


theorem baseBridgeF_of_leaf
    (hfus : FusedModelLeaf) : BaseBridgeF := by
  intro G _ _ z S hcen ⟨ε, hE⟩
  obtain ⟨Gs, iG, fG, p, f, hp, hp2, hq5, htag, ⟨C⟩⟩ := fused_ctx hfus hcen hE
  obtain ⟨σ, hσ⟩ := C.exists_sigma hcen
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine ⟨fun _ => ?_, fun U hUS hU4 hUn => ?_⟩
  · obtain ⟨t, htS, hto, htE⟩ := C.pkg.exists_invol_outside
    obtain ⟨s, hs⟩ := σ.surjective ⟨t, htS⟩
    refine ⟨(s : G), s.2, ?_, ?_⟩
    · intro hmem
      have h1 := (hσ s).1 hmem.2
      rw [hs] at h1
      exact htE h1
    · have h1 : orderOf s = 2 := by
        rw [← MulEquiv.orderOf_eq σ s, hs, Subgroup.orderOf_mk]
        exact hto
      rw [← Subgroup.orderOf_coe s] at h1
      exact h1
  · set ρ : ↥S →* Gs := (C.S₁ : Subgroup Gs).subtype.comp σ.toMonoidHom with hρ
    have hρinj : Function.Injective ρ := Subtype.coe_injective.comp σ.injective
    set V : Subgroup Gs := (U.subgroupOf S).map ρ with hV
    have hVS : V ≤ (C.S₁ : Subgroup Gs) := by
      rintro _ ⟨x, -, rfl⟩
      exact (σ x).2
    have hUe : IsElementaryAbelian 2 ↥U := hU4.1
    have hUsub : IsElementaryAbelian 2 ↥(U.subgroupOf S) := IsElementaryAbelian.subgroupOf hUS
    have hV4 : IVK.IsFourSubgroup V := by
      refine ⟨IsElementaryAbelian.map ρ, ?_⟩
      rw [hV, Subgroup.card_map_of_injective hρinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
      exact hU4.2
    have hVn : ∀ s ∈ (C.S₁ : Subgroup Gs), ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
      intro s hs' v hv
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨s₀, hs₀⟩ := σ.surjective ⟨s, hs'⟩
      have hx' : (x : G) ∈ U := hx
      have hmem : (s₀ : G) * (x : G) * (s₀ : G)⁻¹ ∈ U := hUn (s₀ : G) s₀.2 (x : G) hx'
      refine ⟨s₀ * x * s₀⁻¹, hmem, ?_⟩
      show ((σ (s₀ * x * s₀⁻¹) : ↥(C.S₁ : Subgroup Gs)) : Gs) = s * ((σ x : ↥(C.S₁ : Subgroup Gs)) : Gs) * s⁻¹
      rw [map_mul, map_mul, map_inv, hs₀]
      rfl
    have hVE := C.pkg.four_le hodd hq5 hVS hV4 hVn
    intro u hu
    have hmem : ((σ ⟨u, hUS hu⟩ : ↥(C.S₁ : Subgroup Gs)) : Gs) ∈ V := ⟨⟨u, hUS hu⟩, hu, rfl⟩
    exact (hσ ⟨u, hUS hu⟩).2 (hVE hmem)


theorem baseBridgeF_thm : BaseBridgeF :=
  baseBridgeF_of_leaf fusedModelLeaf

end CFSG.GH74.GLS.Stage1.Main
