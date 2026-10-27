module

public import CFSG.ClassicalInvolution.Asc77.AscE184Graph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem natCard_lt_of_ne_top {Y : Subgroup G} (hY : Y ≠ ⊤) : Nat.card ↥Y < Nat.card G :=
  not_le.mp fun h => hY (Subgroup.eq_top_of_le_card Y h)

theorem MinCex.le_of_section (c : MinCex p f Ω K S R W H) {Y : Subgroup G} (hY : Y ≠ ⊤)
    {K' R' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hKY : K ≤ Y) (hK'Y : K' ≤ Y) (S₁ : Sylow 2 ↥Y)
    (hRS : R.subgroupOf Y ≤ (S₁ : Subgroup ↥Y)) (hR'S : R'.subgroupOf Y ≤ (S₁ : Subgroup ↥Y))
    {W₁ : Subgroup ↥Y} (hW₁ : W₁ ∈ WSet (restrictFamily Ω Y)) (hW₁S : W₁ ≤ (S₁ : Subgroup ↥Y))
    (hW₁n : ∀ s ∈ (S₁ : Subgroup ↥Y), conjSub s W₁ = W₁)
    (h1 : ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ h ∈ H.subgroupOf Y, conjSub h (K.subgroupOf Y) = J)
    (h2 : CentralizersSylowPairs (restrictFamily Ω Y) (K.subgroupOf Y) (H.subgroupOf Y)) :
    Y ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS'⟩ := c.stand.hR
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hEStand : EStand p f (restrictFamily Ω Y) (K.subgroupOf Y) S₁ (R.subgroupOf Y) W₁ :=
    { odd := hp
      five := c.stand.five
      hyp := hΩ.restrict Y
      below := CITBelowU.mono p f (Subgroup.card_le_card_group Y) c.stand.below
      mem := subgroupOf_mem_restrictFamily hK hKY
      aEmpty := AEmpty.restrict hp hΩ hKY c.stand.aEmpty
      twin := ⟨K'.subgroupOf Y, twinSet_subgroupOf hKY hK'Y hK'tw,
        subgroupOf_ne_of_ne hKY hK'Y hK'ne, R'.subgroupOf Y,
        mem_RSet_restrict hK'Ω hK'Y (hΩ.isSylow2In_of_mem_RSet_of_le hp hK'Ω hR' hR'K'),
        Subgroup.subgroupOf_mono Y hR'K', hR'S⟩
      hR := ⟨mem_RSet_restrict hK hKY (hΩ.isSylow2In_of_mem_RSet_of_le hp hK hRR hRK),
        Subgroup.subgroupOf_mono Y hRK, hRS⟩
      hW := ⟨hW₁, hW₁S, hW₁n⟩ }
  have key := c.minimal ↥Y (natCard_lt_of_ne_top hY) (restrictFamily Ω Y) (K.subgroupOf Y) S₁
    (R.subgroupOf Y) W₁ (H.subgroupOf Y) hEStand ⟨h1, h2⟩
  exact Subgroup.subgroupOf_eq_top.mp key

theorem MinCex.trans_of_orbit (c : MinCex p f Ω K S R W H) {Y : Subgroup G} (hKY : K ≤ Y)
    (hY1 : ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ y : Y, conjSub y (K.subgroupOf Y) = J) :
    ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ h ∈ H.subgroupOf Y, conjSub h (K.subgroupOf Y) = J := by
  intro J hJ
  obtain ⟨y, rfl⟩ := hY1 J hJ
  refine ⟨y, ?_, rfl⟩
  have h1 := dstarComp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  have h2 : (conjSub y (K.subgroupOf Y)).map Y.subtype = conjSub (y : G) K := by
    rw [conjSub_subgroupOf Y y K, Subgroup.map_subgroupOf_eq_of_le]
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  rw [h2] at h1
  exact Subgroup.mem_subgroupOf.mpr ((e18_1 p f G Ω K S R W H c).1 y h1)

theorem MinCex.cent_section (c : MinCex p f Ω K S R W H) {Y : Subgroup G} (hKY : K ≤ Y) :
    CentralizersSylowPairs (restrictFamily Ω Y) (K.subgroupOf Y) (H.subgroupOf Y) := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha ha1 ha2
  have hLm := twinSet_map hKY hL
  have hJm := kPerp_map hJ
  have hcm : Commutes (R₁.map Y.subtype) (R₂.map Y.subtype) ∨
      R₂.map Y.subtype = R₁.map Y.subtype := by
    rcases hc with hc | rfl
    · left
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hc x hx y hy)
    · right
      rfl
  have haG : (a : G) ∈ R₁.map Y.subtype ⊔ R₂.map Y.subtype := by
    have : (a : G) ∈ (R₁ ⊔ R₂).map Y.subtype := ⟨a, ha, rfl⟩
    rwa [Subgroup.map_sup] at this
  have hC := c.hyp.cent _ hLm _ hJm _ _ (map_mem_RSet_restrict hR₁) (Subgroup.map_mono hR₁L)
    (map_mem_RSet_restrict hR₂) (Subgroup.map_mono hR₂J) hcm (a : G) haG
    (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hx
  exact Subgroup.mem_subgroupOf.mpr (hC this)

end CFSG.ClassicalInvolution.Asc77
