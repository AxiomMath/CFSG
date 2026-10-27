module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionF5
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Facts

variable {K : Type} [Field K]

theorem lieModel_map_map_e7Levi {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) :
    CFSG.Blueprint.LieModel (((e7Levi K).map e.symm.toMonoidHom).map L.subtype) .E7 0 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  exact LieType.CurtisTits.lieModel_of_mulEquiv (e7LeviMapEquivE8 e)
    (lieModel_e7Levi (F4Pilot.one_le_of_natCard_eq_two_pow hK) hK)

theorem map_e7Levi_le_centralizer_of_le [Finite K] [CharP K 2] {G : Type} [Group G]
    {L : Subgroup G} (e : L ≃* adjointGroup .E8 K) {X : Subgroup G}
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype) :
    ((e7Levi K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
  (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom
      (centralizer_highRootSL2_subgroupOf_E8 (K := K)).symm.le)).trans
    (centralizer_le hXJ)

theorem rootDiagUnit_highDiag_ne_one_E8 [CharP K 2] {c : Kˣ} (hc : c ≠ 1) :
    (⟨rootDiagUnit .E8 (EPilot.highDiag .E8 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inr rfl)) c⟩ :
        adjointGroup .E8 K) ≠ 1 := by
  intro h
  have h1 : rootDiagUnit .E8 (EPilot.highDiag .E8 c) = 1 := congrArg Subtype.val h
  exact hc (EPilot.eq_one_of_commute_pinnedX_highRoot (Or.inr (Or.inr rfl)) (ringChar.eq K 2)
    (by rw [h1]; exact Commute.one_left _))

end Facts

variable {K : Type} [Field K]

theorem neighbour_overgroup_E8_nonsplit_of_not_normal (hcat : E7CatalogueClauses) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E8_nonsplit hset.standard htK.1 ht hKt hK e hAJ hA hcyc hX htX hDe
  have hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_e7Levi_le_centralizer_of_le e hXJ
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hA
    have : 0 < Nat.card K := by rw [hK]; positivity
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab
      (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne)
  exact neighbour_overgroup_E8 hcat hset.kProper hXG htX ht hDX
    (hDe ▸ lieModel_map_map_e7Levi hK e) hcomp hsyl hstd hnn

theorem neighbour_overgroup_E8_nonsplit (hcat : E7CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f :=
  neighbour_overgroup_E8_nonsplit_of_not_normal hcat hset hK e ht hKt hAJ hA hcyc hX htX hDe
    (not_normal_neighbour_E8_of_two_le hset hf hK e ht hKt (Or.inl ⟨A, hAJ, hcyc, hA, hX⟩) hDe)

theorem neighbour_overgroup_E8_of_le_highTorusLine (hcat : E7CatalogueClauses) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c : Kˣ} (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup .E8 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcA : (⟨rootDiagUnit .E8 (EPilot.highDiag .E8 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inr rfl)) c⟩ :
        adjointGroup .E8 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf : 2 ≤ f := by
    have h1 : orderOf c ≤ Nat.card Kˣ := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard c)
    rw [Nat.card_units, hK] at h1
    by_contra hlt
    have h2 : 2 ^ f ≤ 2 := by
      calc 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E8_of_le_highTorusLine hset.standard htK.1 ht hKt hK e hc hAT hcA hX htX
      hDe
  have hnn := not_normal_neighbour_E8_of_le_highTorusLine hset hf hK e ht hKt
    (factF5E8 (by omega) hK) hc hAT hcA hX hDe
  have hTJ : (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K) ≤ posJE8 K :=
    fun _ hx => mem_subgroupOf.2
      (EPilot.highTorusLine_le_highRootSL2 (Or.inr (Or.inr rfl)) (mem_subgroupOf.1 hx))
  have hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (hAT.trans hTJ))
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_e7Levi_le_centralizer_of_le e hXJ
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hcA
    exact rootDiagUnit_highDiag_ne_one_E8 hc1 hcA
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab
      (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne)
  exact neighbour_overgroup_E8 hcat hset.kProper hXG htX ht hDX
    (hDe ▸ lieModel_map_map_e7Levi hK e) hcomp hsyl hstd hnn

theorem neighbour_overgroup_E8_split (hcat : E7CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact neighbour_overgroup_E8_of_le_highTorusLine hcat hset hK e ht hKt hc le_rfl
    (mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)) hX htX hDe

theorem neighbour_overgroup_E8_torus (hcat : E7CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
  · exact neighbour_overgroup_E8_nonsplit hcat hset hf hK e ht hKt hAJ hA hcyc hX htX hDe
  · exact neighbour_overgroup_E8_split hcat hset hf hK e ht hKt hX htX hDe

end CFSG.SeitzReduction.E8Pilot
