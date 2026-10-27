module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecD
public import CFSG.ClassicalInvolution.Asc77.AscE184Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic AscE184Sect

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} {A : Subgroup G}

omit [Finite G] in
theorem exists_of_mem_restrict_sectionFamily {L : Subgroup ↥(sectionHull Ω A)}
    (hL : L ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A)) :
    ∃ J ∈ sectionMembers Ω A, L = (secMember A J).subgroupOf (sectionHull Ω A) := by
  obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hL
  exact ⟨J, hJ, rfl⟩

omit [Finite G] in
theorem subgroupOf_secMember_mem {K : Subgroup G} (hK : K ∈ sectionMembers Ω A) :
    (secMember A K).subgroupOf (sectionHull Ω A) ∈
      restrictFamily (sectionFamily Ω A) (sectionHull Ω A) :=
  subgroupOf_mem_restrictFamily (secMember_mem_sectionFamily hK) (le_sectionHull hK)

theorem mem_kPerp_of_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {L J : Subgroup G} (hL : L ∈ sectionMembers Ω A)
    (hJ : J ∈ sectionMembers Ω A) (h : secMember A J ∈ KPerp (sectionFamily Ω A) (secMember A L)) :
    J ∈ KPerp Ω L := by
  rcases h with h | h
  · exact Or.inl (eq_of_secMember_eq hp hΩ hA hJ hL h)
  · exact Or.inr (mem_omegaNbr_of_sectionFamily hp hq hΩ hA hL hJ h)

theorem MinCex.trans_sectionFamily (c : MinCex p f Ω K S R W H) (hA : IsPGroup 2 ↥A)
    (hKm : K ∈ sectionMembers Ω A)
    (hall : ∀ J ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A),
      ∃ y : ↥(sectionHull Ω A), conjSub y ((secMember A K).subgroupOf (sectionHull Ω A)) = J) :
    ∀ J ∈ dstarComp (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        ((secMember A K).subgroupOf (sectionHull Ω A)),
      ∃ h ∈ (H.subgroupOf (sectionHull Ω A)),
        conjSub h ((secMember A K).subgroupOf (sectionHull Ω A)) = J := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hKY : secMember A K ≤ sectionHull Ω A := le_sectionHull hKm
  intro J hJ
  have hJΛ : J ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A) := by
    rcases dstarComp_subset_insert _ hJ with h | h
    · rw [h]
      exact subgroupOf_secMember_mem hKm
    · exact h
  obtain ⟨y, rfl⟩ := hall J hJΛ
  refine ⟨y, ?_, rfl⟩
  have hyC : (y : G) ∈ Subgroup.centralizer (A : Set G) := sectionHull_le_centralizer Ω A y.2
  have h1 := dstarComp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  have h2 : (conjSub y ((secMember A K).subgroupOf (sectionHull Ω A))).map
      (sectionHull Ω A).subtype = conjSub (y : G) (secMember A K) := by
    rw [conjSub_subgroupOf (sectionHull Ω A) y (secMember A K),
      Subgroup.map_subgroupOf_eq_of_le]
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  rw [h2, conjSub_secMember hyC] at h1
  have h3 := mem_dstarComp_of_dstarComp_sectionFamily hp hq hΩ hA hKm h1 _
    (conjSub_mem_sectionMembers hΩ hyC hKm) rfl
  exact Subgroup.mem_subgroupOf.mpr ((e18_1 p f G Ω K S R W H c).1 y h3)

theorem MinCex.cent_sectionFamily (c : MinCex p f Ω K S R W H) (hA : IsPGroup 2 ↥A)
    (hKm : K ∈ sectionMembers Ω A) :
    CentralizersSylowPairs (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
      ((secMember A K).subgroupOf (sectionHull Ω A)) (H.subgroupOf (sectionHull Ω A)) := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hKY : secMember A K ≤ sectionHull Ω A := le_sectionHull hKm
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha ha1 ha2
  obtain ⟨L₀, hL₀, rfl⟩ := exists_of_mem_restrict_sectionFamily hL.1
  obtain ⟨J₀, hJ₀, rfl⟩ : ∃ J₀ ∈ sectionMembers Ω A,
      J = (secMember A J₀).subgroupOf (sectionHull Ω A) := by
    refine exists_of_mem_restrict_sectionFamily ?_
    rcases hJ with rfl | h
    · exact hL.1
    · exact h.1
  have hL₀Y : secMember A L₀ ≤ sectionHull Ω A := le_sectionHull hL₀
  have hJ₀Y : secMember A J₀ ≤ sectionHull Ω A := le_sectionHull hJ₀
  have hLm := twinSet_map hKY hL
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y] at hLm
  have hJm := kPerp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y, Subgroup.map_subgroupOf_eq_of_le hJ₀Y] at hJm
  have hLtw : L₀ ∈ twinSet Ω K := mem_twinSet_of_secMember hp hq hΩ hA hKm hL₀ hLm
  have hJperp : J₀ ∈ KPerp Ω L₀ := mem_kPerp_of_sectionFamily hp hq hΩ hA hL₀ hJ₀ hJm
  have hR₁Ω : R₁.map (sectionHull Ω A).subtype ∈ RSet Ω :=
    mem_RSet_of_mem_RSet_sectionFamily hA (map_mem_RSet_restrict hR₁)
  have hR₂Ω : R₂.map (sectionHull Ω A).subtype ∈ RSet Ω :=
    mem_RSet_of_mem_RSet_sectionFamily hA (map_mem_RSet_restrict hR₂)
  have hR₁L₀ : R₁.map (sectionHull Ω A).subtype ≤ L₀ := by
    refine (Subgroup.map_mono hR₁L).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y]
    exact secMember_le_left A L₀
  have hR₂J₀ : R₂.map (sectionHull Ω A).subtype ≤ J₀ := by
    refine (Subgroup.map_mono hR₂J).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJ₀Y]
    exact secMember_le_left A J₀
  have hcm : Commutes (R₁.map (sectionHull Ω A).subtype) (R₂.map (sectionHull Ω A).subtype) ∨
      R₂.map (sectionHull Ω A).subtype = R₁.map (sectionHull Ω A).subtype := by
    rcases hc with hc | rfl
    · left
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hc x hx y hy)
    · right
      rfl
  have haG : (a : G) ∈ R₁.map (sectionHull Ω A).subtype ⊔ R₂.map (sectionHull Ω A).subtype := by
    have : (a : G) ∈ (R₁ ⊔ R₂).map (sectionHull Ω A).subtype := ⟨a, ha, rfl⟩
    rwa [Subgroup.map_sup] at this
  have hC := c.hyp.cent L₀ hLtw J₀ hJperp _ _ hR₁Ω hR₁L₀ hR₂Ω hR₂J₀ hcm (a : G) haG
    (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hx
  exact Subgroup.mem_subgroupOf.mpr (hC this)

@[expose] def sectionGood (Ω : Set (Subgroup G)) (A K : Subgroup G)
    (L : Subgroup ↥(sectionHull Ω A)) : Prop :=
  ∃ J ∈ sectionMembers Ω A, L = (secMember A J).subgroupOf (sectionHull Ω A) ∧
    J ∈ dstarComp Ω K

theorem sectionGood_step (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K : Subgroup G} {L L' : Subgroup ↥(sectionHull Ω A)}
    (hL' : L' ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
    (hgood : sectionGood Ω A K L)
    (hadj : dstarAdj (restrictFamily (sectionFamily Ω A) (sectionHull Ω A)) L L') :
    sectionGood Ω A K L' := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', rfl⟩ := exists_of_mem_restrict_sectionFamily hL'
  have h1 := dstarAdj_map hadj
  rw [Subgroup.map_subgroupOf_eq_of_le (le_sectionHull hJ),
    Subgroup.map_subgroupOf_eq_of_le (le_sectionHull hJ')] at h1
  exact ⟨J', hJ', rfl, hJK.tail (dstarAdj_of_sectionFamily hp hq hΩ hA hJ hJ' h1)⟩

theorem MinCex.sectionGood_le_H (c : MinCex p f Ω K S R W H) {L : Subgroup ↥(sectionHull Ω A)}
    (hgood : sectionGood Ω A K L) : L.map (sectionHull Ω A).subtype ≤ H := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  rw [Subgroup.map_subgroupOf_eq_of_le (le_sectionHull hJ)]
  exact (secMember_le_left A J).trans (c.le_H_of_mem_dstarComp hJK)

end CFSG.ClassicalInvolution.Asc77
