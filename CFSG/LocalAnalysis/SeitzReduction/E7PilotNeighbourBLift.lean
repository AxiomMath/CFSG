module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldCoverBLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {K : Type} [Field K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_center_of_mem_oddCore_of_commute_E7 [Finite K] [CharP K 2]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .E7 K) {A Y : Subgroup (adjointGroup .E7 K)}
    (hA : centralizer (A : Set (adjointGroup .E7 K)) = Y ⊔ perpLevi .E7 K)
    (hYD : Y ≤ centralizer (perpLevi .E7 K : Set (adjointGroup .E7 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .E7 K))) (hYodd : Odd (Nat.card Y))
    (hYA : Y ≤ A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) :=
  E6Pilot.mem_center_of_mem_oddCore_of_commute_sup_of_fix hL htC ht hK e
    exists_eq_conj_of_fix_perpLevi_E7 center_perpLevi_E7_eq_bot isQuasisimple_perpLevi_E7 hA hYD
    hYc hYodd hYA hX htX

theorem mem_center_of_mem_oddCore_of_commute_nonsplit_E7 (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {A : Subgroup (adjointGroup .E7 K)}
    (hAJ : A ≤ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K))
    (hA : Nat.card A = Nat.card K + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hKc
  obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E7 hq hAJ hA hcyc
  have hodd : Odd (Nat.card A) := by
    rw [hA, hKc]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact mem_center_of_mem_oddCore_of_commute_E7 hL htC ht hK e hcent hAD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) hodd le_rfl hX htX

theorem mem_center_of_mem_oddCore_of_commute_highTorusLine_E7
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E7 K)
    {X : Subgroup G} (hX : X = (((highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) :
    ∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (X : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  exact mem_center_of_mem_oddCore_of_commute_E7 hL htC ht hK e (centralizer_highTorusLine_E7 hq)
    highTorusLine_le_centralizer_perpLevi_E7 E6Pilot.highTorusLine_subgroupOf_le_centralizer_self
    (odd_card_highTorusLine_E7 hKc) le_rfl hX htX

end CFSG.SeitzReduction.E7Pilot
