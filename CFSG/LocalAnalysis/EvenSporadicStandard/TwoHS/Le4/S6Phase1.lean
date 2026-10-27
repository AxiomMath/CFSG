module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverFours

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_fourHyp_twoHS
    (h : StdHyp G L) (hZ : Nat.card (center L) = 2)
    (hq : IsSporadic (L ⧸ center L) .HS) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : Nat.card S = 4) : ∃ f : G, FourHyp G L f := by
  obtain ⟨f, hf4, hCf, hZf, hN⟩ := h.card_four_structure hZ S hS
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  exact ⟨f, ⟨h, hZ, index_dvd_two_of_isSporadic_hs hq, center_eq_bot_of_isSporadic_hs hq,
    tightCoverFacts_of_isSporadic_hs hZ hq, hf4, hCf, hZf, hN⟩⟩

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.solomon_lemma_two_one_twoHS
    (h : StdHyp G L) (hZ : Nat.card (center L) = 2)
    (hq : IsSporadic (L ⧸ center L) .HS) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : Nat.card S = 4) :
    ∃ f : G, FourHyp G L f ∧ ∃ s y : G, IsTight L s ∧ y * y = 1 ∧ y * f * y⁻¹ = f⁻¹ ∧
      y ∉ L ⊔ zpowers f ∧ centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y ∧
      (∃ g : G, y = g * f ^ 2 * g⁻¹) ∧ (∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹) ∧
      (¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) ∧
      ∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  obtain ⟨f, H⟩ := h.exists_fourHyp_twoHS hZ hq S hS
  exact ⟨f, H, H.exists_phase_one (foursGroupCondition_of_isSporadic_cover_hs hZ hq) S hS⟩

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.solomon_lemma_two_one_sylow
    (h : StdHyp G L) (hZ : Nat.card (center L) = 2)
    (hq : IsSporadic (L ⧸ center L) .HS) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : Nat.card S = 4) :
    ∃ f : G, FourHyp G L f ∧ ∃ s y : G, IsTight L s ∧ y * y = 1 ∧ y * f * y⁻¹ = f⁻¹ ∧
      y ∉ L ⊔ zpowers f ∧ centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y ∧
      (∃ g : G, y = g * f ^ 2 * g⁻¹) ∧ (∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹) ∧
      (¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) ∧
      (∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L) ∧
      ∃ S₀ : Subgroup G, f ∈ S₀ ∧ S₀ ≤ centralizer ({f ^ 2} : Set G) ∧
        S₀ ≤ centralizer ({s ^ 2} : Set G) ∧ IsPGroup 2 S₀ ∧
        ¬ 2 ∣ S₀.relIndex (centralizer ({f ^ 2} : Set G)) ∧
        ∃ n : G, (∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀) ∧ n * f ^ 2 * n⁻¹ = s ^ 2 := by
  obtain ⟨f, H, s, y, hs, hyy, hyf, hy, hN, hyc, hsc, hn, hu⟩ :=
    h.solomon_lemma_two_one_twoHS hZ hq S hS
  refine ⟨f, H, s, y, hs, hyy, hyf, hy, hN, hyc, hsc, hn, hu, ?_⟩
  have hodd := H.odd_relIndex_centralizer (classFacts_of_isSporadic_hs hq) hs hn hsc
  rw [← H.norm] at hodd
  obtain ⟨u, hu, -⟩ := hu
  have hfC : f ∈ centralizer (L : Set G) := H.mem_cent
  have hfz : f ∈ centralizer ({s ^ 2} : Set G) ⊓ centralizer ({f ^ 2} : Set G) := by
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · rw [← hu]; exact (mem_centralizer_iff.1 hfC u u.2).symm
    · group
  exact exists_sylow_fusion hsc hodd hfz (isPGroup_zpowers_of_orderOf_eq_four H.order)

end CFSG.EvenSporadicStandard.TwoHS
