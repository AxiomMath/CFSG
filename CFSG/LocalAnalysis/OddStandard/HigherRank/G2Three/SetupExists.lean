module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SetupFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setup

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


private theorem isQuasisimple_of_open {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  haveI hQperf : Group.IsPerfect Q := ⟨h1⟩
  refine ⟨hQperf, h2, ?_⟩
  by_contra hc
  push Not at hc
  haveI hperf' : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ center Q)
      (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  have hbot : _root_.commutator (Q ⧸ center Q) = ⊥ := by
    rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  have htop : (⊤ : Subgroup (Q ⧸ center Q)) = ⊥ :=
    (Group.IsPerfect.commutator_eq_top (G := Q ⧸ center Q)).symm.trans hbot
  haveI := h2.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ center Q)
  exact hx (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top x))

private theorem isSylowIn_map_subtype {V : Subgroup G} (P : Sylow 2 ↥V) :
    IsSylowIn 2 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem exists_setting3 (hF : G23Facts) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    ∃ s : Setting3 G L, s.t = t := by
  classical
  have hqsOpen : CFSG.Open.IsQuasisimple ↥L := hS.std.standard.1
  haveI hLperf : Group.IsPerfect ↥L := ⟨hqsOpen.1⟩
  have hqs : CFSG.IsQuasisimple ↥L := isQuasisimple_of_open hqsOpen
  have hcenter : Nat.card (center ↥L) ∣ 3 := card_center_dvd_three hLperf hL
  have hoddZ : Odd (Nat.card (center ↥L)) :=
    Odd.of_dvd_nat (by decide : Odd 3) hcenter
  let S₀ : Sylow 2 ↥L := default
  obtain ⟨fr, fr', hfacts, hlift, -, hsylowS⟩ :=
    exists_frame_lift hF hqs hoddZ hL S₀
  obtain ⟨hLH, -, -⟩ := normal_centralizer hS ht ht2
  let H : Subgroup G := centralizer ({t} : Set G)
  let X : Subgroup G := L ⊔ centIn H L
  have hXH : X ≤ H := sup_le hLH inf_le_left
  have hSX : fr.S ≤ X := hsylowS.1.trans le_sup_left
  have hSsub : IsPGroup 2 (fr.S.subgroupOf X) := hsylowS.2.1.comap_subtype (K := X)
  obtain ⟨PX, hSPX⟩ := hSsub.exists_le_sylow
  let R : Subgroup G := (PX : Subgroup ↥X).map X.subtype
  have hsylowR : IsSylowIn 2 X R := isSylowIn_map_subtype PX
  have hSR : fr.S ≤ R := by
    intro s hs
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hSX hs⟩, hSPX (by rw [Subgroup.mem_subgroupOf]; exact hs), rfl⟩
  have hRH : R ≤ H := hsylowR.1.trans hXH
  have hRsub : IsPGroup 2 (R.subgroupOf H) := hsylowR.2.1.comap_subtype (K := H)
  obtain ⟨PT, hRPT⟩ := hRsub.exists_le_sylow
  let T : Subgroup G := (PT : Subgroup ↥H).map H.subtype
  have hsylowT : IsSylowIn 2 H T := isSylowIn_map_subtype PT
  have hRT : R ≤ T := by
    intro s hs
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hRH hs⟩, hRPT (by rw [Subgroup.mem_subgroupOf]; exact hs), rfl⟩
  refine ⟨⟨fr, fr', hfacts, hlift, hsylowS, t, ht, ht2, R, T, ?_, ?_, hSR, hRT⟩, rfl⟩
  · change IsSylowIn 2 X R
    exact hsylowR
  · change IsSylowIn 2 H T
    exact hsylowT

end Setup

end CFSG.OddStandard.HigherRank.G2Three
