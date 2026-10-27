module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5


theorem card_le_of_involution_three (hE : MonsterExistenceStatement MGriess)
    (hco1 : Co1ThreeRankFact) (hbaby : BabyThreeRankFact) (t : MGriess) (ht : orderOf t = 2)
    (E : Subgroup MGriess) (hEt : E ≤ Subgroup.centralizer ({t} : Set MGriess))
    (hEe : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 6 := by
  obtain ⟨-, a, z, -, -, -, hcls, hA, hZ, -⟩ := id hE
  rcases hcls t ht with h | h
  · obtain ⟨-, hz, ⟨e⟩⟩ := hA t h
    have hZ2 : Nat.card (Subgroup.center (cent t)) = 2 ^ 1 := by
      rw [← Subgroup.card_map_of_injective (cent t).subtype_injective, hz, Nat.card_zpowers, ht,
        pow_one]
    exact card_le_of_le_quot Nat.prime_three (by norm_num) (IsPGroup.of_card hZ2) hbaby e hEt hEe
  · obtain ⟨-, -, -, ⟨e⟩, -, -⟩ := hZ t h
    exact card_le_of_le_quot Nat.prime_three (by norm_num) CFSG.pCore_isPGroup hco1
      (e.trans CFSG.Sporadic.Co1Block.co1MatEquiv) hEt hEe

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
