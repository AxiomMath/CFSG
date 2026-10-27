module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516J
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB

theorem leafAt_M
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_M
    (N := 808017424794512875886459904961710757005754368000000000)
    (fun _ => by
      obtain ⟨E⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
      rw [Nat.card_congr E.toEquiv, YGroups.Y443.natCard_Gmat_eq_monsterOrder]
      norm_num [Open.monsterOrder])
    [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1),
      (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]
    (by decide) (by decide) (Qs := {3, 5, 7}) (by decide)
    (fun hs q hq t ht B hB h => by
      refine (by decide : ∀ q ∈ ({3, 5, 7} : Finset ℕ),
        ¬ 2 ^ 41 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2) q hq ?_
      rw [← h, Nat.mul_div_cancel _ two_pos]
      exact (CatLeafProof.monsterLocalComponentsInput S hs ⟨e⟩ t ht B hB).1)

end CFSG.ComponentClassification.SolMax.Spor516
