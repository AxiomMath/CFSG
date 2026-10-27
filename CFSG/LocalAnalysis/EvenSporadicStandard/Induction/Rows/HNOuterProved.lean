module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNLink

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section


theorem hnOuterInvCent_proved : HNOuterInvCent := by
  intro X _ hX σ hσ2 hout
  obtain ⟨e⟩ := hX
  have e' : X ≃* NativeSporadic.HN := e
  have hσ1 : σ ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hout' : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rintro ⟨g, hg⟩
    exact hout ⟨g, hg.symm⟩
  obtain ⟨f⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e' σ hord hout'
  have hsub : fixSubgroup σ = CFSG.Sporadic.Schreier.fixSub σ := Subgroup.ext fun _ => Iff.rfl
  rw [hsub, Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Nat.le_of_eq (by decide)

end

end CFSG.EvenSporadicStandard.Induction
