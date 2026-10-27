module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourPosition
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaNeighbourAlternative
  OmegaCatalogueClausesAt)


section Facts

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}

noncomputable def perpLeviMapEquivE7' (e : L ≃* adjointGroup .E7 K) :
    EPilot.perpLevi .E7 K ≃*
      (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  ((EPilot.perpLevi .E7 K).equivMapOfInjective _ e.symm.injective).trans
    (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem center_map_map_perpLevi_E7_eq_bot [Finite K] [CharP K 2] (e : L ≃* adjointGroup .E7 K) :
    center (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) = ⊥ := by
  rw [← Subgroup.map_center_eq (perpLeviMapEquivE7' e), center_perpLevi_E7_eq_bot,
    Subgroup.map_bot]

theorem odd_card_center_map_map_perpLevi_E7 [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E7 K) :
    Odd (Nat.card (center (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype))) := by
  rw [center_map_map_perpLevi_E7_eq_bot e, card_bot]
  exact odd_one

theorem lieModel_quotient_center_map_map_perpLevi_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E7 K) :
    CFSG.Blueprint.LieModel
      ((((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) ⧸
        center (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype))
      .POmegaPlus 6 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ (perpLeviMapEquivE7' e) (Subgroup.map_center_eq _))
    (lieModel_perpLevi_E7_quotient_center hK)

theorem rootDiagUnit_highDiag_ne_one_E7 [CharP K 2] {c : Kˣ} (hc : c ≠ 1) :
    (⟨rootDiagUnit .E7 (EPilot.highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ :
        adjointGroup .E7 K) ≠ 1 := by
  intro h
  have h1 : rootDiagUnit .E7 (EPilot.highDiag .E7 c) = 1 := congrArg Subtype.val h
  exact hc (EPilot.eq_one_of_commute_pinnedX_highRoot (Or.inr (Or.inl rfl)) (ringChar.eq K 2)
    (by rw [h1]; exact Commute.one_left _))

theorem natCard_map_map_E7 (e : L ≃* adjointGroup .E7 K) (A : Subgroup (adjointGroup .E7 K)) :
    Nat.card ((A.map e.symm.toMonoidHom).map L.subtype) = Nat.card A := by
  rw [card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective]

theorem highTorusLine_subgroupOf_le_posJE7 :
    (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) ≤ posJE7 K :=
  fun _ hx => mem_subgroupOf.2
    (EPilot.highTorusLine_le_highRootSL2 (Or.inr (Or.inl rfl)) (mem_subgroupOf.1 hx))

theorem six_ne_four_pair (f : ℕ) : ((6 : ℕ), f) ≠ (4, 1) := by
  intro h
  have := congrArg Prod.fst h
  norm_num at this

end Facts

variable {K : Type} [Field K]

theorem neighbour_overgroup_E7_of_standard (hcat : OmegaCatalogueClausesAt 6) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hnn := not_normal_neighbour_E7_holds hset hf hK e ht hKt hXodd hXJ hDe hsyl
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_perpLevi_le_centralizer_E7 hq e hXJ
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab hXne
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_perpLevi_E7 e
  have hDm := lieModel_quotient_center_map_map_perpLevi_E7 hK e (G := G) (L := L)
  have hZD := odd_card_center_map_map_perpLevi_E7 e (G := G) (L := L)
  rw [← hDe] at hDm hZD
  exact OmegaPilot.neighbour_overgroup_omega (six_ne_four_pair f) hcat hset.kProper hXG htX ht
    hDX hDq (Or.inl rfl) hDm hZD hcomp hsyl hstd hnn

theorem neighbour_overgroup_E7_nonsplit (hcat : OmegaCatalogueClausesAt 6) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E7_nonsplit hset.standard htK.1 ht hKt hK hq e hAJ hA hcyc hX htX hDe
  have hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, natCard_map_map_E7, hA, hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hA
    have : 0 < Nat.card K := by rw [hK]; positivity
    omega
  exact neighbour_overgroup_E7_of_standard hcat hset hf hK e ht hKt
    (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne) hXodd hXJ htX hDe hcomp hsyl hstd

theorem neighbour_overgroup_E7_of_le_highTorusLine (hcat : OmegaCatalogueClausesAt 6) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c : Kˣ} (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .E7 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K))
    (hcA : (⟨rootDiagUnit .E7 (EPilot.highDiag .E7 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inl rfl)) c⟩ :
        adjointGroup .E7 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E7_of_le_highTorusLine hset.standard htK.1 ht hKt hK e hc hAT hcA hX htX
      hDe
  have hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (hAT.trans highTorusLine_subgroupOf_le_posJE7))
  have hXodd : Odd (Nat.card X) := by
    rw [hX, natCard_map_map_E7]
    exact (odd_card_highTorusLine_E7 hK).of_dvd_nat (Subgroup.card_dvd_of_le hAT)
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hcA
    exact rootDiagUnit_highDiag_ne_one_E7 hc1 hcA
  exact neighbour_overgroup_E7_of_standard hcat hset hf hK e ht hKt
    (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne) hXodd hXJ htX hDe hcomp hsyl hstd

theorem neighbour_overgroup_E7_split (hcat : OmegaCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : X = (((EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact neighbour_overgroup_E7_of_le_highTorusLine hcat hset hf hK e ht hKt hc le_rfl
    (mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)) hX htX hDe

end CFSG.SeitzReduction.E7Pilot
