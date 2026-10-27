module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ABGLocalTools

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {R M N : Subgroup G}

theorem le_of_isPGroup_of_not_dvd_relIndex (hR : IsPGroup p R) (hRM : R ≤ M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (h : ¬ p ∣ N.relIndex M) : R ≤ N := by
  haveI : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hNidx : N.relIndex M = Nat.card (↥M ⧸ N.subgroupOf M) := by
    show (N.subgroupOf M).index = _
    exact (Subgroup.index_eq_card _).symm
  have hcard : ¬ p ∣ Nat.card (↥M ⧸ N.subgroupOf M) := by
    rw [← hNidx]
    exact h
  intro g hg
  have hgM : g ∈ M := hRM hg
  let f : ↥M →* ↥M ⧸ N.subgroupOf M := QuotientGroup.mk' (N.subgroupOf M)
  have himg : IsPGroup p ((R.subgroupOf M).map f) := (hR.comap_subtype).map f
  have hcarddvd : Nat.card ((R.subgroupOf M).map f) ∣ Nat.card (↥M ⧸ N.subgroupOf M) :=
    Subgroup.card_subgroup_dvd_card _
  have hnotdvd : ¬ p ∣ Nat.card ((R.subgroupOf M).map f) := fun hd => hcard (hd.trans hcarddvd)
  have hbot : (R.subgroupOf M).map f = ⊥ := by
    rcases himg.card_eq_or_dvd with h1 | hd
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd hd hnotdvd
  have hmem : f ⟨g, hgM⟩ ∈ (R.subgroupOf M).map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hg)
  rw [hbot] at hmem
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (⟨g, hgM⟩ : ↥M)).mp (Subgroup.mem_bot.mp hmem))

namespace IsSylowOf

theorem centralizes_of_mem_normalizer_of_isMulCommutative {H : Type*} [Group H] [Finite H]
    {r : ℕ} [Fact r.Prime] {P : Subgroup H} (hP : IsSylowOf r P ⊤)
    (hPc : IsMulCommutative P) {x : H} (hx : x ∈ Subgroup.normalizer (P : Set H))
    (hxr : IsPGroup r (Subgroup.zpowers x)) :
    ∀ p ∈ P, x * p = p * x := by
  have hT : IsPGroup r (P ⊔ Subgroup.zpowers x : Subgroup H) :=
    hP.isPGroup.to_sup_of_normal_left' hxr (Subgroup.zpowers_le.mpr hx)
  have hTP : (P ⊔ Subgroup.zpowers x : Subgroup H) = P :=
    hP.eq_of_le le_sup_left le_top hT
  have hxP : x ∈ P := by
    have hmem : x ∈ P ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hTP] at hmem
  intro p hp
  exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hxP⟩ ⟨p, hp⟩)

end IsSylowOf

end CFSG.ABGLocalTools
