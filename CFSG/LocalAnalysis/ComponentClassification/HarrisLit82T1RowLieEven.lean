module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36EvenOddCore

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowLie

open CFSG Subgroup

theorem false_of_lieChar_two
    {S : Type} [Group S] [Finite S] (hS : LieChar 2 S) {t : S} (ht : orderOf t = 2)
    {J : Subgroup S} (hJC : J ≤ centralizer {t})
    (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal) (hJq : IsTwoQuasisimple ↥J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, n, f, hm⟩ := hS
  have hfree := CatLeaf.involutionCentralizersComponentFree_of_evenLieType
    ⟨τ, n, f, N36.admissible_of_lieModel' hm, hm⟩
  have hO := N36.EvenOddCore.evenLieInvolutionOddCoreFact_holds S τ n f hm t ht
  set C := centralizer ({t} : Set S)
  set B := J.subgroupOf C
  have hBO : pPrimeCore 2 ↥B = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 B hJs, hO]
    exact Subgroup.bot_subgroupOf B
  have hBq : IsTwoQuasisimple ↥B :=
    isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC).symm hJq
  have hBqs : IsQuasisimple ↥B := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hBO).trans QuotientGroup.quotientBot) hBq.2
  exact hfree t ht B ⟨hBqs, hJs⟩

end CFSG.ComponentClassification.HarrisLit.T1.RowLie
