module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFbar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec63PT_embed_comp {G : Type} [Group G] [Finite G] (Y : Subgroup G) {b₀ : ↥Y}
    {Vb₀ : Subgroup ↥Y}
    (hc : IsComponentIn Vb₀ (centralizer ({b₀} : Set ↥Y))) (hL : IsL29 Vb₀)
    (hu : ∀ K : Subgroup ↥Y, IsComponentIn K (centralizer ({b₀} : Set ↥Y)) → K = Vb₀) :
    IsComponentIn (Vb₀.map Y.subtype) (Y ⊓ centralizer ({(b₀ : G)} : Set G)) ∧
      IsL29 (Vb₀.map Y.subtype) ∧ InFStar (Vb₀.map Y.subtype) ∧
      ∀ K : Subgroup G, IsComponentIn K (Y ⊓ centralizer ({(b₀ : G)} : Set G)) →
        K = Vb₀.map Y.subtype := by
  have hι : Function.Injective Y.subtype := Y.subtype_injective
  have hmap : (centralizer ({b₀} : Set ↥Y)).map Y.subtype =
      Y ⊓ centralizer ({(b₀ : G)} : Set G) := sec63PT_map_subtype_centralizer Y b₀
  have hcomp : IsComponentIn (Vb₀.map Y.subtype) (Y ⊓ centralizer ({(b₀ : G)} : Set G)) := by
    rw [← hmap]
    exact (sec63PT_isComponentIn_map_iff Y.subtype hι).mpr hc
  have hL29 : IsL29 (Vb₀.map Y.subtype) := (sec63PT_isL29_map_iff Y.subtype hι).mpr hL
  have hF : InFStar (Vb₀.map Y.subtype) := by
    show IsFStarGroup (Vb₀.map Y.subtype)
    exact Or.inr ⟨hcomp.isQuasisimple, Or.inl hL29⟩
  refine ⟨hcomp, hL29, hF, ?_⟩
  intro K hK
  have hKY : K ≤ Y := hK.1.trans inf_le_left
  have hKmap : (K.comap Y.subtype).map Y.subtype = K :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hKY)
  have hK' : IsComponentIn (K.comap Y.subtype) (centralizer ({b₀} : Set ↥Y)) := by
    refine (sec63PT_isComponentIn_map_iff Y.subtype hι).mp ?_
    rw [hKmap, hmap]
    exact hK
  rw [← hKmap, hu (K.comap Y.subtype) hK']

theorem sec63PT_embed_two {G : Type} [Group G] (Y : Subgroup G) {V₀ Vb₀ : Subgroup ↥Y}
    {b₀ : ↥Y}
    (h2 : ∀ Q : Subgroup ↥Y, IsPGroup 2 Q →
      Q ≤ V₀ ⊓ centralizer ({b₀} : Set ↥Y) ⊓ centralizer (Vb₀ : Set ↥Y) → Nat.card Q ≤ 2) :
    ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ V₀.map Y.subtype ⊓ centralizer ({(b₀ : G)} : Set G) ⊓
        centralizer ((Vb₀.map Y.subtype : Subgroup G) : Set G) → Nat.card P ≤ 2 := by
  intro P hP hle
  have hPY : P ≤ Y :=
    ((hle.trans inf_le_left).trans inf_le_left).trans (Subgroup.map_subtype_le V₀)
  have hP' : IsPGroup 2 (P.subgroupOf Y) := sec63PT_isPGroup_subgroupOf hPY hP
  have hle' : P.subgroupOf Y ≤
      V₀ ⊓ centralizer ({b₀} : Set ↥Y) ⊓ centralizer (Vb₀ : Set ↥Y) := by
    intro y hy
    have hyP : (y : G) ∈ P := hy
    have hle_y := hle hyP
    have hyA : (y : G) ∈ V₀.map Y.subtype := hle_y.1.1
    have hyB : (y : G) ∈ centralizer ({(b₀ : G)} : Set G) := hle_y.1.2
    have hyC : (y : G) ∈
        centralizer ((Vb₀.map Y.subtype : Subgroup G) : Set G) := hle_y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_map_iff_mem Y.subtype_injective).mp hyA
    · change y ∈ Subgroup.centralizer ({b₀} : Set ↥Y)
      rw [Subgroup.mem_centralizer_singleton_iff] at hyB ⊢
      exact Subtype.ext hyB
    · change y ∈ Subgroup.centralizer (Vb₀ : Set ↥Y)
      rw [Subgroup.mem_centralizer_iff] at hyC ⊢
      intro v hv
      exact Subtype.ext (hyC (v : G) ⟨v, hv, rfl⟩)
  have h := h2 (P.subgroupOf Y) hP' hle'
  rwa [sec63PT_card_subgroupOf hPY] at h

theorem sec63PT_embed_R {G : Type} [Group G] (Y : Subgroup G) {V₀ : Subgroup ↥Y} {b₀ : ↥Y}
    {R₀ : Subgroup ↥Y} (h2 : IsPGroup 2 R₀) (hle : R₀ ≤ V₀ ⊓ centralizer ({b₀} : Set ↥Y))
    (h8 : Nat.card R₀ = 8) (hgen : R₀ = closure {r : ↥Y | r ∈ R₀ ∧ orderOf r = 2}) :
    IsPGroup 2 (R₀.map Y.subtype) ∧
      R₀.map Y.subtype ≤ V₀.map Y.subtype ⊓ centralizer ({(b₀ : G)} : Set G) ∧
      Nat.card (R₀.map Y.subtype) = 8 ∧
      R₀.map Y.subtype = closure {r : G | r ∈ R₀.map Y.subtype ∧ orderOf r = 2} := by
  have hι : Function.Injective Y.subtype := Y.subtype_injective
  refine ⟨h2.map Y.subtype, ?_, ?_, sec63PT_map_subtype_closure hgen⟩
  · intro r hr
    rcases Subgroup.mem_map.mp hr with ⟨v, hv, rfl⟩
    have hvle := hle hv
    have hv1 : v ∈ V₀ := hvle.1
    have hv2 : v ∈ centralizer ({b₀} : Set ↥Y) := hvle.2
    refine ⟨⟨v, hv1, rfl⟩, ?_⟩
    change Y.subtype v ∈ Subgroup.centralizer ({(b₀ : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hv2 ⊢
    exact congrArg Subtype.val hv2
  · rw [Subgroup.card_map_of_injective hι, h8]

theorem sec63PT_fact_of_factAt {G : Type} [Group G] [Finite G] (Y : Subgroup G) {x : G}
    (hx : x * x = 1)
    (hxN : x ∈ normalizer (Y : Set G)) (hF : Sec63PTFactAt ↥Y (conjAut Y hx hxN))
    {V : Subgroup G} (hV : IsComponentIn V (Y ⊓ centralizer ({x} : Set G))) (hVL : IsL29 V)
    {b : G} (hbV : b ∈ V) (hb : orderOf b = 2) :
    IsI4PlusIn Y b ∨
      ∃ Vb : Subgroup G, IsComponentIn Vb (Y ⊓ centralizer ({b} : Set G)) ∧ IsL29 Vb ∧
        InFStar Vb ∧
        (∀ K : Subgroup G, IsComponentIn K (Y ⊓ centralizer ({b} : Set G)) → K = Vb) ∧
        (∀ P : Subgroup G, IsPGroup 2 P →
          P ≤ V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) → Nat.card P ≤ 2) ∧
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ V ⊓ centralizer ({b} : Set G) ∧ Nat.card R = 8 ∧
          R = closure {r : G | r ∈ R ∧ orderOf r = 2} := by
  have hι : Function.Injective Y.subtype := Y.subtype_injective
  have hfix : (fixSub (conjAut Y hx hxN)).map Y.subtype =
      Y ⊓ centralizer ({x} : Set G) := sec63PT_map_subtype_fixSub Y hx hxN
  have hVY : V ≤ Y := hV.1.trans inf_le_left
  let V₀ : Subgroup ↥Y := V.comap Y.subtype
  have hVeq : V₀.map Y.subtype = V :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hVY)
  have hV₀ : IsComponentIn V₀ (fixSub (conjAut Y hx hxN)) := by
    refine (sec63PT_isComponentIn_map_iff Y.subtype hι).mp ?_
    rw [hVeq, hfix]
    exact hV
  have hVL₀ : IsL29 V₀ :=
    (sec63PT_isL29_map_iff Y.subtype hι).mp (by rw [hVeq]; exact hVL)
  have hbY : b ∈ Y := (hV.1 hbV).1
  let b₀ : ↥Y := ⟨b, hbY⟩
  have hb₀V₀ : b₀ ∈ V₀ := hbV
  have hb₀2 : orderOf b₀ = 2 := by
    change orderOf (⟨b, hbY⟩ : ↥Y) = 2
    rw [Subgroup.orderOf_mk, hb]
  rcases hF V₀ hV₀ hVL₀ b₀ hb₀V₀ hb₀2 with hpocket |
      ⟨Vb₀, hc, hL, hu, h2, R₀, hR2, hR₀le, hR8, hRgen⟩
  · exact Or.inl (isI4PlusIn_of_top hbY hpocket)
  · have hcomp := sec63PT_embed_comp Y hc hL hu
    obtain ⟨hcG, hLG, hFG, huG⟩ := hcomp
    have htwo := sec63PT_embed_two Y h2
    have hR := sec63PT_embed_R Y hR2 hR₀le hR8 hRgen
    rw [← hVeq]
    refine Or.inr ⟨Vb₀.map Y.subtype, hcG, hLG, hFG, huG, htwo, ?_⟩
    exact ⟨R₀.map Y.subtype, hR⟩

end CFSG.OddStandard.SmallF3.Omega
