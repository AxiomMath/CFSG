module

public import CFSG.CharacterTheory.TwoRankLowerBound.BinarySummandExchange
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteSummandCoordinates

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe vectorUniverse

theorem finite_local_endomorphism_summand_exchange (ring : Type*) [Ring ring] :
    ∀ (size : ℕ) (vector : Fin size → Type vectorUniverse)
      [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)],
      (∀ label, ∀ operator : Module.End ring (vector label), IsUnit operator ∨ IsUnit (1 - operator)) →
      ∀ projection : Module.End ring (∀ label, vector label), IsIdempotentElem projection →
        ∃ support : Set (Fin size),
          Nonempty (projection.range ≃ₗ[ring] supportedCoordinateSubmodule (ring := ring) vector support) := by
  intro size
  induction size with
  | zero =>
    intro vector _ _ _ projection _
    exact ⟨∅, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ size hinduction =>
    intro vector _ _ hlocal projection hidempotent
    let equivalence := finiteProductConsEquiv (ring := ring) vector
    let productProjection := transportedProjection equivalence projection
    have hproductIdempotent : IsIdempotentElem productProjection :=
      transportedProjection_isIdempotent equivalence projection hidempotent
    obtain ⟨remainder, hremainder, hcases⟩ := binary_local_endomorphism_summand_exchange
      (hlocal 0) productProjection hproductIdempotent
    obtain ⟨support, ⟨tailEquivalence⟩⟩ := hinduction
      (fun label : Fin size => vector label.succ) (fun label => hlocal label.succ) remainder hremainder
    obtain ⟨rangeEquivalence⟩ := transportedProjection_range_equiv equivalence projection
    rcases hcases with hproductEquivalence | hremainderEquivalence
    · obtain ⟨productEquivalence⟩ := hproductEquivalence
      exact ⟨{label | label = 0 ∨ ∃ member ∈ support, member.succ = label},
        ⟨rangeEquivalence.trans (productEquivalence.trans
          ((LinearEquiv.prodCongr (LinearEquiv.refl ring (vector 0)) tailEquivalence).trans
            (supportedCoordinatesConsEquiv vector support).symm))⟩⟩
    · obtain ⟨remainderEquivalence⟩ := hremainderEquivalence
      exact ⟨{label | ∃ member ∈ support, member.succ = label},
        ⟨rangeEquivalence.trans (remainderEquivalence.trans
          (tailEquivalence.trans (supportedCoordinatesTailEquiv vector support).symm))⟩⟩

end CFSG.TwoRankLowerBound.Helpers
