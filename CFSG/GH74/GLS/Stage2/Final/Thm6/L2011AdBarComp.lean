module

public import CFSG.GH74.GLS.Stage2.Local.P34Bar
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.LocalCores

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barIn_mono' {H X Y : Subgroup G} (h : X ≤ Y) : barIn H X ≤ barIn H Y := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hk)), rfl⟩

theorem isQuasisimple_barIn {H K : Subgroup G} (hKH : K ≤ H) (hq : IsQuasisimple ↥K) :
    IsQuasisimple ↥(barIn H K) := by
  have hKH' : IsQuasisimple ↥(K.subgroupOf H) :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hq
  refine isQuasisimple_map hKH' (mkH H) ?_
  intro hle
  rw [QuotientGroup.ker_mk'] at hle
  have hodd : Odd (Nat.card ↥(K.subgroupOf H)) :=
    Odd.of_dvd_nat (odd_card_pPrimeCore H) (Subgroup.card_dvd_of_le hle)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have := isQuasisimple_nontrivial hKH'
  have := hKH'.1
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem isComponent_barIn {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx2 : orderOf x = 2)
    {K : Subgroup G} (hKH : K ≤ H) (hKC : K ≤ centralizer ({x} : Set G))
    (hq : IsQuasisimple ↥K) (hsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal) :
    IsComponent ((barIn H K).subgroupOf (centralizer ({mkH H ⟨x, hxH⟩} : Set (HBar H)))) := by
  set Y : Subgroup (HBar H) := centralizer ({mkH H ⟨x, hxH⟩} : Set (HBar H)) with hY
  have hYeq : Y = barIn H (Cen x) := centralizer_mk_eq H hx2 hxH
  have hKY : barIn H K ≤ Y := hYeq ▸ barIn_mono' hKC
  refine ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKY).symm
    (isQuasisimple_barIn hKH hq), ?_⟩
  have hDC : Cen x ⊓ H ≤ Cen x := inf_le_left
  have hsubD : (K.subgroupOf (Cen x ⊓ H)).IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.comap (Subgroup.inclusion hDC) hsub
    have h2 : (K.subgroupOf (centralizer ({x} : Set G))).comap (Subgroup.inclusion hDC) =
        K.subgroupOf (Cen x ⊓ H) := by
      ext d
      exact Iff.rfl
    rwa [h2] at h1
  let ρ : ↥(Cen x ⊓ H) →* ↥Y :=
    ((mkH H).comp (Subgroup.inclusion (inf_le_right : Cen x ⊓ H ≤ H))).codRestrict Y (fun d => by
      rw [hYeq]
      exact ⟨⟨d, (Subgroup.mem_inf.1 d.2).2⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 d.2).1, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [hYeq] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    exact ⟨⟨h, Subgroup.mem_subgroupOf.1 hh, h.2⟩, Subtype.ext rfl⟩
  have hmap : (K.subgroupOf (Cen x ⊓ H)).map ρ = (barIn H K).subgroupOf Y := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨d, hd, hdy⟩
      have hdy' : mkH H ⟨d, (Subgroup.mem_inf.1 d.2).2⟩ = y := congrArg Subtype.val hdy
      rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨d, (Subgroup.mem_inf.1 d.2).2⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hd), hdy'⟩
    · intro hyK
      obtain ⟨h, hh, hhy⟩ := Subgroup.mem_subgroupOf.1 hyK
      have hhK : (h : G) ∈ K := Subgroup.mem_subgroupOf.1 hh
      exact ⟨⟨h, hKC hhK, h.2⟩, Subgroup.mem_subgroupOf.2 hhK, Subtype.ext hhy⟩
  rw [← hmap]
  exact hsubD.map hρ

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
