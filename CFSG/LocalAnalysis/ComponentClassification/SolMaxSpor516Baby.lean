module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516J
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB

theorem leafAt_B
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .B) :
    CF516LeafAt S :=
  leafAt_of_filter e BMCase.sporadicOddCoreFree_B (N := 4154781481226426191177580544000000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .B) =
        Nat.card NativeSporadic.B from rfl, CatLeaf.card_nativeB'])
    [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1),
      (47, 1)]
    (by decide) (by decide) (Qs := {3, 5}) (by decide)
    (fun _ q hq t ht K hK h => by
      refine (by decide : ∀ q ∈ ({3, 5} : Finset ℕ), ¬ 17 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2) q
        hq ?_
      rw [← h, Nat.mul_div_cancel _ two_pos]
      exact (Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
        ⟨e⟩ t ht K hK).2.2)

end CFSG.ComponentClassification.SolMax.Spor516
