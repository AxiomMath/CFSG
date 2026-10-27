module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwoHR7
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStab
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt)


section Facts

variable {K : Type} [Field K]

theorem lieModel_map_map_a5Levi {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) :
    CFSG.Blueprint.LieModel (((a5Levi K).map e.symm.toMonoidHom).map L.subtype) .PSL 6 2 f :=
  LieType.CurtisTits.lieModel_of_mulEquiv (a5LeviMapEquiv e) (lieModel_a5Levi hK)

theorem rootDiagUnit_highDiag_ne_one [CharP K 2] {c : Kˣ} (hc : c ≠ 1) :
    (⟨rootDiagUnit .E6 (EPilot.highDiag .E6 c),
      rootDiagUnit_highDiag_mem_adjointGroup (Or.inl rfl) c⟩ : adjointGroup .E6 K) ≠ 1 := by
  intro h
  have h1 : rootDiagUnit .E6 (EPilot.highDiag .E6 c) = 1 := congrArg Subtype.val h
  exact hc (EPilot.eq_one_of_commute_pinnedX_highRoot (Or.inl rfl) (ringChar.eq K 2)
    (by rw [h1]; exact Commute.one_left _))

theorem zLeviOTwo_of_four_le [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : ZLeviOTwo K :=
  eq_bot_of_normal_isPGroup_perfectCore_zDLevi hq

end Facts

variable {K : Type} [Field K]

theorem neighbour_overgroup_E6_nonsplit_of_not_normal (hcat : SLmCatalogueClausesAt 6)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E6_nonsplit_of_one_le hset.standard htK.1 ht hKt hf hK e hAJ hA hcyc hX
      htX hDe
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_a5Levi_le_centralizer e hXJ
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hA
    have : 0 < Nat.card K := by rw [hK]; positivity
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab
      (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne)
  exact neighbour_overgroup_E6 hcat hset.kProper hXG htX ht hDX
    (hDe ▸ lieModel_map_map_a5Levi hK e) hcomp hsyl hstd hnn

theorem neighbour_overgroup_E6_nonsplit (hcat : SLmCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E6 K)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact neighbour_overgroup_E6_nonsplit_of_not_normal hcat hset hK e ht hKt hAJ hA hcyc hX htX hDe
    (not_normal_neighbour_E6_nonsplit hset hf hK e ht hKt (zLeviOTwo_of_four_le hq)
      (factF56E6_of_factF5E6 hq hF5) hAJ hA hcyc hX hDe)

theorem neighbour_overgroup_E6_of_le_highTorusLine (hcat : SLmCatalogueClausesAt 6) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E6 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E6 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))
    (hcA : (⟨rootDiagUnit .E6 (EPilot.highDiag .E6 c),
      rootDiagUnit_highDiag_mem_adjointGroup (Or.inl rfl) c⟩ : adjointGroup .E6 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
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
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
    exact odd_card_highTorusLine hf1 hK
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E6_of_centralizer_eq_sup hset.standard htK.1 ht hKt hf hK e
      (centralizer_eq_highTorusLine_sup_of_le (Or.inl rfl) hc hAT hcA)
      highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
      hTodd hX htX hDe
  have hnn := not_normal_neighbour_E6_of_le_highTorusLine hset hf hK e ht hKt
    (zLeviOTwo_of_four_le hq) (factF56E6_of_factF5E6 hq hF5) hc hAT hcA hX hDe
  have hTJ : (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K) ≤ posJ K :=
    fun _ hx => mem_subgroupOf.2
      (EPilot.highTorusLine_le_highRootSL2 (Or.inl rfl) (mem_subgroupOf.1 hx))
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (hAT.trans hTJ))
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_a5Levi_le_centralizer e hXJ
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hcA
    exact rootDiagUnit_highDiag_ne_one hc1 hcA
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab
      (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne)
  exact neighbour_overgroup_E6 hcat hset.kProper hXG htX ht hDX
    (hDe ▸ lieModel_map_map_a5Levi hK e) hcomp hsyl hstd hnn

theorem neighbour_overgroup_E6_split (hcat : SLmCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E6 K) {X : Subgroup G}
    (hX : X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact neighbour_overgroup_E6_of_le_highTorusLine hcat hset hK e ht hKt hF5 hc le_rfl
    (mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)) hX htX hDe

theorem neighbour_overgroup_E6_torus (hcat : SLmCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E6 K) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
  · exact neighbour_overgroup_E6_nonsplit hcat hset hf hK e ht hKt hF5 hAJ hA hcyc hX htX hDe
  · exact neighbour_overgroup_E6_split hcat hset hf hK e ht hKt hF5 hX htX hDe

end CFSG.SeitzReduction.E6Pilot
