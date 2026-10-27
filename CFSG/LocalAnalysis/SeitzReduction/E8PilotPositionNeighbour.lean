module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutDHR7

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem not_normal_neighbour_E8_nonsplit {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E8 K)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      hA, hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact not_normal_map_oddCore_neighbour_E8 hset hf hK e ht hKt hF5 hXodd hXJ hDe
    (neighbour_standard_E8_nonsplit hset.standard htC ht hKt hK e hAJ hA hcyc hX htX hDe).2.1

theorem not_normal_neighbour_E8_of_le_highTorusLine {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E8 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E8 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcA : (⟨rootDiagUnit .E8 (EPilot.highDiag .E8 c),
      E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup (Or.inr (Or.inr rfl)) c⟩ :
        adjointGroup .E8 K) ∈ A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf1 : 1 ≤ f := by omega
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hTJ : (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K) ≤ posJE8 K :=
    fun _ hx => mem_subgroupOf.2
      (EPilot.highTorusLine_le_highRootSL2 (Or.inr (Or.inr rfl)) (mem_subgroupOf.1 hx))
  have hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (hAT.trans hTJ))
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (E6Pilot.highTorusLine_le_adjointGroup (Or.inr (Or.inr rfl)))).toEquiv]
    exact E6Pilot.odd_card_highTorusLine hf1 hK
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective]
    exact Odd.of_dvd_nat hTodd (card_dvd_of_le hAT)
  exact not_normal_map_oddCore_neighbour_E8 hset hf hK e ht hKt hF5 hXodd hXJ hDe
    (neighbour_standard_E8_of_le_highTorusLine hset.standard htC ht hKt hK e hc hAT hcA hX htX
      hDe).2.1

theorem not_normal_neighbour_E8_split {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E8 K) {X : Subgroup G}
    (hX : X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
      e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact not_normal_neighbour_E8_of_le_highTorusLine hset hf hK e ht hKt hF5 hc le_rfl
    (mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)) hX hDe

theorem not_normal_neighbour_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E8 K) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
        e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
  · exact not_normal_neighbour_E8_nonsplit hset hf hK e ht hKt hF5 hAJ hA hcyc hX hDe
  · exact not_normal_neighbour_E8_split hset hf hK e ht hKt hF5 hX hDe

end CFSG.SeitzReduction.E8Pilot
