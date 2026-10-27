module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquiv

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

section Cert


theorem exists_twoHSFacts_of_isF5Centralizer {H : Type} [Group H] {E : Subgroup H}
    (h : TwoHS.IsF5Centralizer H E) : ∃ a z b z₁ : H, TwoHSFacts H a z b z₁ := by
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_p1408_of_isF5Centralizer h
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  have hF : TwoHS.IsF5Centralizer ↥P1408 (E.map (Ψ : H →* ↥P1408)) :=
    Section3.isF5Centralizer_map' Ψ h
  have hE : ∀ x : ↥P1408, x ∈ E.map (Ψ : H →* ↥P1408) ↔
      (x : Equiv.Perm (Fin 1408)) ∈ blocks1408 := fun x => by
    refine (Subgroup.mem_map_equiv (f := Ψ)).trans ?_
    rw [hΨ, MulEquiv.apply_symm_apply]
  exact exists_twoHSFacts_of_mulEquiv ⟨pA, pZ, pB, pZ₁, twoHSFacts_P1408 hP hF hE⟩ Ψ

theorem twoHSInterface : TwoHSInterface where
  nonempty_mulEquiv := fun H H' _ _ E E' h h' => isF5Centralizer_nonempty_mulEquiv H H' E E' h h'
  facts := fun _ _ _ h => exists_twoHSFacts_of_isF5Centralizer h

end Cert

end CFSG.EvenSporadicStandard.HNRecog
