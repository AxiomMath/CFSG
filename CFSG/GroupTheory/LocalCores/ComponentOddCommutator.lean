module

public import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeEvenClassification.QuasisimpleCore
import CFSG.CGT.PushingUpLit.CGT6.Emb5CompBasic

public section

namespace CFSG.LocalCores

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem centralizes_of_commutator_le_odd {S N R : Subgroup X}
    (hS : IsComponent S) (hNodd : Odd (Nat.card N))
    (hSN : S ≤ normalizer (N : Set X)) (hRN : R ≤ normalizer (N : Set X))
    (hcomm : ⁅S, R⁆ ≤ N) : S ≤ centralizer (R : Set X) := by
  let Y : Subgroup X := S ⊔ N ⊔ R
  have hSY : S ≤ Y := le_sup_left.trans le_sup_left
  have hNY : N ≤ Y := le_sup_right.trans le_sup_left
  have hYn : Y ≤ normalizer (N : Set X) :=
    sup_le (sup_le hSN Subgroup.le_normalizer) hRN
  have hNn : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).2 hYn
  have hSc : IsComponent (S.subgroupOf Y) := LocalCores.component_overgroup hS hSY
  have hSNcomm : ⁅S, N⁆ = ⊥ := by
    rcases LocalCores.component_normal_subgroup hSc hNn with hle | hc
    · have hSNle : S ≤ N := fun s hs => hle (show (⟨s, hSY hs⟩ : Y) ∈ S.subgroupOf Y from hs)
      have hdvd : Nat.card S ∣ Nat.card N := Subgroup.card_dvd_of_le hSNle
      exact False.elim ((Nat.not_even_iff_odd.mpr hNodd)
        ((CFSG.CGT.PushingUpLit.CGT6.even_card_of_isComponent hS).two_dvd.trans hdvd
          |> even_iff_two_dvd.mpr))
    · have hm := congrArg (Subgroup.map Y.subtype) hc
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSY,
        Subgroup.map_subgroupOf_eq_of_le hNY, Subgroup.map_bot] at hm
      exact hm
  have hNcent : N ≤ centralizer (S : Set X) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rwa [Subgroup.commutator_comm N S]
  exact CFSG.RankThreeEvenClassification.Helpers.perfect_centralizes_of_commutator_central
    S R hS.1.1 (hcomm.trans hNcent)

theorem mem_centralizer_of_commutator_mem_odd {S N : Subgroup X}
    (hS : IsComponent S) (hNodd : Odd (Nat.card N))
    (hSN : S ≤ normalizer (N : Set X)) {r : X}
    (hrN : r ∈ normalizer (N : Set X))
    (hcomm : ∀ s ∈ S, ⁅s, r⁆ ∈ N) : r ∈ centralizer (S : Set X) := by
  have hzN : zpowers r ≤ normalizer (N : Set X) := zpowers_le.mpr hrN
  have hc : ⁅S, zpowers r⁆ ≤ N := by
    simpa only [Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure] using
      (TauCeti.commutator_closure_closure_le (X := (S : Set X)) (Y := ({r} : Set X))
        (N := N) (by simpa using hSN)
        (by simpa only [← Subgroup.zpowers_eq_closure] using hzN)
        (by intro s hs t ht; obtain rfl := Set.mem_singleton_iff.mp ht; exact hcomm s hs))
  have hSc := centralizes_of_commutator_le_odd hS hNodd hSN hzN hc
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (Subgroup.mem_centralizer_iff.mp (hSc hs) r (mem_zpowers r)).symm

end CFSG.LocalCores

end
