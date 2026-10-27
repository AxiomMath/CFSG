module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReachRow

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.RuStd CFSG.EvenSporadicStandard.Induction.RuSz

section Proved


theorem ruPair_analysis {G : Type} [Group G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic ↥L .Ru) (hQ : RuPair G L K u) :
    IsSimpleGroup ↥K ∧ SuzukiModel ↥K 2 3 ∧
      (∀ c ∈ L ⊓ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      Nat.card ↥(L ⊓ centralizer (K : Set G)) = 4 := by
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  set u' : ↥L := ⟨u, huL⟩ with hu'
  have hu2' : orderOf u' = 2 := by rw [hu', Subgroup.orderOf_mk]; exact hu2
  have hKu' : ∀ k ∈ K.subgroupOf L, k * u' = u' * k := fun k hk =>
    Subtype.ext (hKu (k : G) (Subgroup.mem_subgroupOf.1 hk))
  have hcardKl : Nat.card (K.subgroupOf L) = 29120 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hcard
  obtain ⟨hs, hSz, hnorm, hcent⟩ := pair_analysis hL hu2' hKu' hcardKl
  refine ⟨(MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hKL)).1 hs,
    suzukiModel_of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm hSz, ?_, ?_⟩
  · intro c hc k hk
    have hcL : c ∈ L := hc.1
    have hcu : (⟨c, hcL⟩ : ↥L) * u' = u' * ⟨c, hcL⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc.2)
    exact Subgroup.mem_subgroupOf.1
      (hnorm ⟨c, hcL⟩ hcu ⟨k, hKL hk⟩ (Subgroup.mem_subgroupOf.2 hk))
  · rw [← card_centralizer_subgroupOf hKL]
    exact hcent

theorem ruSuzukiModel_proved : RuSuzukiModel := fun _ _ _ _ _ hL hQ =>
  (ruPair_analysis hL hQ).2.1

theorem ruLocalFacts_proved : RuLocalFacts where
  exists_pair G _ L hL := by
    obtain ⟨u, Kl, hu2, hKu, hcard⟩ := exists_pair_Y hL
    refine ⟨Kl.map L.subtype, (u : G), u.2, by rw [Subgroup.orderOf_coe]; exact hu2,
      Subgroup.map_subtype_le Kl, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact congrArg Subtype.val (hKu k hk)
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hcard
  simple _ _ _ _ _ hL hQ := (ruPair_analysis hL hQ).1
  normal G _ L K u hL hQ := by
    refine ⟨fun n hn g => ?_⟩
    have hn' := Subgroup.mem_subgroupOf.1 hn
    rw [Subgroup.mem_subgroupOf]
    exact (ruPair_analysis hL hQ).2.2.1 g g.2 n hn'
  card_centralizer _ _ _ _ _ hL hQ := (ruPair_analysis hL hQ).2.2.2

end Proved

end CFSG.EvenSporadicStandard.Induction
