module

public import CFSG.Assembly.OddCoreElimination.Preparation

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup CFSG.LargeEvenClassification CFSG.Assembly.Dichotomy

theorem connected_completed_odd_core_span_normal {G : Type*} [Group G] [Finite G]
    (hconn : Conn3 G)
    (hspan : ∀ D ∈ E3 G, Odd (Nat.card (oddCoreSpan D)) ∧
      D ≤ normalizer (oddCoreSpan D : Set G) ∧
      ∀ d ∈ D, d ≠ 1 → oddCoreSpan D ⊓ centralizer ({d} : Set G) = involutionOddCore d) :
    ∀ A ∈ E3 G, (oddCoreSpan A).Normal ∧ ∀ B ∈ E3 G, oddCoreSpan B = oddCoreSpan A := by
  have hcomplete : ∀ D : Subgroup G, CFSG.Open.IsElemAbelian 2 D → Nat.card D = 8 →
      OddCoreSpanCompleted D := fun D hD hcard => by
    obtain ⟨h1, h2, h3⟩ := hspan D ⟨hD, hcard⟩
    exact ⟨h2, h1, h3⟩
  have heq : ∀ A ∈ E3 G, ∀ B ∈ E3 G, oddCoreSpan B = oddCoreSpan A := fun A hA B hB =>
    oddCoreSpan_eq_of_rankThreeSubgroupPath hcomplete (hconn.2 ⟨B, hB⟩ ⟨A, hA⟩)
  intro A hA
  refine ⟨⟨fun x hx g => ?_⟩, fun B hB => heq A hA B hB⟩
  have hAg : A.map (MulAut.conj g).toMonoidHom ∈ E3 G :=
    ⟨Helpers.elementary_map A hA.1 _,
      (card_map_of_injective (MulAut.conj g).injective).trans hA.2⟩
  have h := oddCoreSpan_map (MulAut.conj g) A
  rw [heq A hA _ hAg] at h
  rw [← h]
  exact ⟨x, hx, rfl⟩

end CFSG.ComponentClassification.UnbalancedGS
