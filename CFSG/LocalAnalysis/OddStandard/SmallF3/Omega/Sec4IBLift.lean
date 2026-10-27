module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBRho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBSyl
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def sec4ILiftB (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    (fr : Sec4IFrame Sec4IQ) (P : Subgroup G) : Subgroup G :=
  ((P.subgroupOf L) ⊓ (sec4IB0 fr).comap (sec4IRho e)).map L.subtype

@[expose] noncomputable def sec4ILiftPhi (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    (fr : Sec4IFrame Sec4IQ) (P : Subgroup G) (v : Fin 7 → ZMod 2) : G := by
  classical
  exact if h : ∃ x : ↥L, (x : G) ∈ P ∧ sec4IRho e x = sec4IPsi fr v then
    ((Classical.choose h : ↥L) : G) else 1

theorem mem_sec4ILiftB_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (fr : Sec4IFrame Sec4IQ)
    (P : Subgroup G) {x : G} :
    x ∈ sec4ILiftB e fr P ↔ ∃ hx : x ∈ L, x ∈ P ∧ sec4IRho e ⟨x, hx⟩ ∈ sec4IB0 fr := by
  rw [sec4ILiftB]
  constructor
  · intro hx
    change ∃ y : ↥L, y ∈ (P.subgroupOf L) ⊓ (sec4IB0 fr).comap (sec4IRho e) ∧
      L.subtype y = x at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyP, hyB⟩ := hy
    subst hyx
    exact ⟨y.2, hyP, hyB⟩
  · rintro ⟨hxL, hxP, hxB⟩
    change ∃ y : ↥L, y ∈ (P.subgroupOf L) ⊓ (sec4IB0 fr).comap (sec4IRho e) ∧
      L.subtype y = x
    exact ⟨⟨x, hxL⟩, ⟨hxP, hxB⟩, rfl⟩

theorem sec4ILiftB_le (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (fr : Sec4IFrame Sec4IQ)
    (P : Subgroup G) : sec4ILiftB e fr P ≤ P := by
  intro x hx
  exact ((mem_sec4ILiftB_iff e fr P).mp hx).2.1

theorem sec4ILiftB_le_L (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (fr : Sec4IFrame Sec4IQ)
    (P : Subgroup G) : sec4ILiftB e fr P ≤ L := by
  intro x hx
  exact ((mem_sec4ILiftB_iff e fr P).mp hx).1

private theorem sec4ILiftB_subgroupOf_isPGroup (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    (fr : Sec4IFrame Sec4IQ) (P : Subgroup G) (hP : IsSylow2Of P L) :
    IsPGroup 2 ↥((sec4ILiftB e fr P).subgroupOf L) := by
  have hP2 : IsPGroup 2 ↥(P.subgroupOf L) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  exact hP2.to_le (Subgroup.subgroupOf_mono L (sec4ILiftB_le e fr P))

variable [Finite G]

theorem sec4ILiftPhi_spec (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) :
    ∃ hx : sec4ILiftPhi e fr P v ∈ L, sec4ILiftPhi e fr P v ∈ P ∧
      sec4IRho e ⟨sec4ILiftPhi e fr P v, hx⟩ = sec4IPsi fr v := by
  have hvR : sec4IPsi fr v ∈ (P.subgroupOf L).map (sec4IRho e) :=
    hfr.le (sec4IPsi_mem_sec4IB0 fr hv)
  rw [Subgroup.mem_map] at hvR
  obtain ⟨x, hxP, hxeq⟩ := hvR
  have h : ∃ x : ↥L, (x : G) ∈ P ∧ sec4IRho e x = sec4IPsi fr v := ⟨x, hxP, hxeq⟩
  unfold sec4ILiftPhi
  rw [dif_pos h]
  exact ⟨(Classical.choose h).2, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

theorem sec4ILiftPhi_mem (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) : sec4ILiftPhi e fr P v ∈ sec4ILiftB e fr P := by
  obtain ⟨hxL, hxP, hxρ⟩ := sec4ILiftPhi_spec hL e hP hfr hv
  rw [mem_sec4ILiftB_iff]
  exact ⟨hxL, hxP, hxρ ▸ sec4IPsi_mem_sec4IB0 fr hv⟩

theorem sec4ILift_card_le (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) {F : Subgroup G} (hFP : F ≤ P)
    (hF : CFSG.Open.IsElemAbelian 2 F) :
    Nat.card F ≤ 2 ^ 6 ∧
      (Nat.card F = 2 ^ 6 → (F.subgroupOf L).map (sec4IRho e) = sec4IB0 fr) := by
  have hFL : F ≤ L := hFP.trans hP.1
  have hFel : CFSG.Open.IsElemAbelian 2 (F.subgroupOf L) :=
    CFSG.Open.IsElemAbelian.subgroupOf hF L
  have hF2 : IsPGroup 2 ↥(F.subgroupOf L) := CFSG.Open.IsElemAbelian.isPGroup hFel
  have hcardF : Nat.card (F.subgroupOf L) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv
  have hsub : F.subgroupOf L ≤ P.subgroupOf L := Subgroup.subgroupOf_mono L hFP
  have hmap_le : (F.subgroupOf L).map (sec4IRho e) ≤ (P.subgroupOf L).map (sec4IRho e) :=
    Subgroup.map_mono (f := sec4IRho e) hsub
  have hmapEl : CFSG.Open.IsElemAbelian 2 ((F.subgroupOf L).map (sec4IRho e)) :=
    sec4IRho_isElemAbelian_map e hFel
  have hcardMap : Nat.card ((F.subgroupOf L).map (sec4IRho e)) = Nat.card (F.subgroupOf L) :=
    natCard_map_sec4IRho hL e hF2
  refine ⟨?_, ?_⟩
  · have hle := hfr.card_le ((F.subgroupOf L).map (sec4IRho e)) hmap_le hmapEl
    rwa [hcardMap, hcardF] at hle
  · intro hcard
    have hcard' : Nat.card ((F.subgroupOf L).map (sec4IRho e)) = 2 ^ 6 := by
      rw [hcardMap, hcardF, hcard]
    exact hfr.eq_B0 ((F.subgroupOf L).map (sec4IRho e)) hmap_le hmapEl hcard'

theorem sec4ILift_map_eq (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ((sec4ILiftB e fr P).subgroupOf L).map (sec4IRho e) = sec4IB0 fr := by
  apply le_antisymm
  · rintro y ⟨b, hb, rfl⟩
    have hb' : (b : G) ∈ sec4ILiftB e fr P := hb
    exact ((mem_sec4ILiftB_iff e fr P).mp hb').2.2
  · intro y hy
    have hyR : y ∈ (P.subgroupOf L).map (sec4IRho e) := hfr.le hy
    rw [Subgroup.mem_map] at hyR
    obtain ⟨x, hxP, hxρ⟩ := hyR
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, hxρ⟩
    have hρ : sec4IRho e x ∈ sec4IB0 fr := by rwa [hxρ]
    exact (mem_sec4ILiftB_iff e fr P).mpr ⟨x.2, hxP, hρ⟩

private theorem sec4ILiftB_subgroupOf_isElemAbelian (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {P : Subgroup G} (hP : IsSylow2Of P L)
    {fr : Sec4IFrame Sec4IQ} (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    CFSG.Open.IsElemAbelian 2 ((sec4ILiftB e fr P).subgroupOf L) := by
  refine sec4IRho_isElemAbelian_of_map hL e
    (sec4ILiftB_subgroupOf_isPGroup e fr P hP) ?_
  rw [sec4ILift_map_eq hL e hP hfr]
  exact sec4IB0_isElemAbelian fr

theorem sec4ILift_card (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    Nat.card (sec4ILiftB e fr P) = 2 ^ 6 := by
  have hBL : sec4ILiftB e fr P ≤ L := sec4ILiftB_le_L e fr P
  have h2 : IsPGroup 2 ↥((sec4ILiftB e fr P).subgroupOf L) :=
    sec4ILiftB_subgroupOf_isPGroup e fr P hP
  calc
    Nat.card (sec4ILiftB e fr P)
        = Nat.card ((sec4ILiftB e fr P).subgroupOf L) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv).symm
    _ = Nat.card (((sec4ILiftB e fr P).subgroupOf L).map (sec4IRho e)) :=
          (natCard_map_sec4IRho hL e h2).symm
    _ = Nat.card (sec4IB0 fr) := by rw [sec4ILift_map_eq hL e hP hfr]
    _ = 2 ^ 6 := sec4IB0_card fr

theorem sec4ILift_isMax (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    IsMaxElemAbelianIn P (sec4ILiftB e fr P) := by
  have hBL : sec4ILiftB e fr P ≤ L := sec4ILiftB_le_L e fr P
  have hBel : CFSG.Open.IsElemAbelian 2 (sec4ILiftB e fr P) := by
    have hmap := CFSG.Open.IsElemAbelian.map
      (sec4ILiftB_subgroupOf_isElemAbelian hL e hP hfr) L.subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le hBL] at hmap
  refine ⟨sec4ILiftB_le e fr P, hBel, ?_⟩
  intro B'' hB''le hB''el
  have h1 := (sec4ILift_card_le hL e hP hfr hB''le hB''el).1
  rwa [sec4ILift_card hL e hP hfr]

theorem sec4ILift_unique (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    ∀ B' : Subgroup G, IsMaxElemAbelianIn P B' → B' = sec4ILiftB e fr P := by
  intro B' hB'
  obtain ⟨hB'le, hB'el, hB'max⟩ := hB'
  obtain ⟨hBle, hBel, _⟩ := sec4ILift_isMax hL e hP hfr
  have hcardB : Nat.card (sec4ILiftB e fr P) = 2 ^ 6 := sec4ILift_card hL e hP hfr
  have hcardB_le : Nat.card (sec4ILiftB e fr P) ≤ Nat.card B' := hB'max _ hBle hBel
  have hle' : Nat.card B' ≤ 2 ^ 6 := (sec4ILift_card_le hL e hP hfr hB'le hB'el).1
  have hge : 2 ^ 6 ≤ Nat.card B' := by rw [← hcardB]; exact hcardB_le
  have hcardB' : Nat.card B' = 2 ^ 6 := le_antisymm hle' hge
  have hmapB' : (B'.subgroupOf L).map (sec4IRho e) = sec4IB0 fr :=
    (sec4ILift_card_le hL e hP hfr hB'le hB'el).2 hcardB'
  have hle : B' ≤ sec4ILiftB e fr P := by
    intro b hb
    have hbL : b ∈ L := hB'le.trans hP.1 hb
    rw [mem_sec4ILiftB_iff]
    refine ⟨hbL, hB'le hb, ?_⟩
    rw [← hmapB', Subgroup.mem_map]
    exact ⟨⟨b, hbL⟩, hb, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle hcardB_le

end CFSG.OddStandard.SmallF3.Omega
