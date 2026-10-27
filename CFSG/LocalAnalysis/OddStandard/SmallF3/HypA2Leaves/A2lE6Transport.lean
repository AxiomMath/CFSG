module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup

variable {G X : Type*} [Group G] [Group X]

theorem a2lE6_map_centralizer_singleton {C : Type*} [Group C] (e : C ≃* X) (c : C) :
    (centralizer ({c} : Set C)).map (e : C →* X) = centralizer ({e c} : Set X) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    change e y * e c = e c * e y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx

theorem a2lE6_comap_centralizer (C A : Subgroup G) (hCA : C ≤ A) {d : G} (hd : d ∈ C) :
    ((A ⊓ centralizer ({d} : Set G)) ⊓ C).comap C.subtype =
      centralizer ({(⟨d, hd⟩ : C)} : Set C) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨-, hx⟩, -⟩
    exact Subtype.ext hx
  · intro hx
    exact ⟨⟨hCA x.2, congrArg Subtype.val hx⟩, x.2⟩

theorem a2lE6_component_transport (C : Subgroup G) (e : X ≃* C) {A H T₀ : Subgroup G} {d : G}
    (hd : d ∈ C) (hdH : d ∈ H) (hCA : C ≤ A)
    (hH : CFSG.Assembly.IsComponentOf H (A ⊓ centralizer ({d} : Set G))) (hHC : H ⊓ C = T₀)
    (hq : CFSG.Assembly.IsQuasisimple T₀) :
    ∃ (T : Subgroup X) (φ : T ≃* T₀),
      CFSG.Assembly.IsComponentOf T (centralizer ({e.symm ⟨d, hd⟩} : Set X)) ∧
      ∃ hz : e.symm ⟨d, hd⟩ ∈ T, ((φ ⟨e.symm ⟨d, hd⟩, hz⟩ : T₀) : G) = d := by
  have hT₀C : T₀ ≤ C := hHC ▸ inf_le_right
  have hdT : d ∈ T₀ := hHC ▸ ⟨hdH, hd⟩
  have hsub := ((hH.2.1.inf C).comap C.subtype).map (e.symm : C →* X)
  rw [hHC, a2lE6_comap_centralizer C A hCA hd,
    a2lE6_map_centralizer_singleton e.symm] at hsub
  have hdT' : (⟨d, hd⟩ : C) ∈ T₀.subgroupOf C := hdT
  let T : Subgroup X := (T₀.subgroupOf C).map (e.symm : C →* X)
  let ε : T ≃* T₀.subgroupOf C := (e.symm.subgroupMap (T₀.subgroupOf C)).symm
  let φ : T ≃* T₀ := ε.trans (Subgroup.subgroupOfEquivOfLe hT₀C)
  have hzT : e.symm ⟨d, hd⟩ ∈ T := ⟨⟨d, hd⟩, hdT', rfl⟩
  refine ⟨T, φ, ⟨hsub.le, hsub, ?_⟩, hzT, ?_⟩
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv φ hq
  · have : ε ⟨e.symm ⟨d, hd⟩, hzT⟩ = ⟨⟨d, hd⟩, hdT'⟩ := by
      show (e.symm.subgroupMap (T₀.subgroupOf C)).symm _ = _
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    change ((ε ⟨e.symm ⟨d, hd⟩, hzT⟩ : T₀.subgroupOf C) : G) = d
    rw [this]

end CFSG.OddStandard.SmallF3.HypA2Leaves
