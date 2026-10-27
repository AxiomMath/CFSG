module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Recognition.OrderFifteen
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.StrongEmbedding

public section

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G]

theorem lyons_unitary_four_sylow_strong_embedding [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) ∧
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) := by
  obtain ⟨-, -, hd, -⟩ := lyons_unitary_four_normalizer_odd_quotient hnonab hT S U hSU
  rcases hd with hd | hd
  · obtain ⟨-, hcent, hemb⟩ :=
      lyons_order_three_normalized_odd_subgroups_and_strong_embedding hnonab hT S U hSU hd
    exact ⟨fun e he he1 => (hcent e he he1).1.trans (hcent e he he1).2.symm, hemb⟩
  · obtain ⟨hcent, hemb, -⟩ :=
      lyons_order_fifteen_centralizers_and_strong_embedding hnonab hT S U hSU hd
    exact ⟨hcent, hemb⟩

end CFSG.LyonsUnitaryFour
