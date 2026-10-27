module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Recognition.StrongEmbedding
public import CFSG.LocalAnalysis.LyonsUnitaryFour.StrongEmbeddingRecognition

public section

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G]

theorem lyons_unitary_four_recognition_of_sylow
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (h : ∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2 := by
  obtain ⟨H, _, U, hH, hSU⟩ := h
  obtain ⟨-, hemb⟩ := lyons_unitary_four_sylow_strong_embedding hnonab hH S U hSU
  obtain ⟨hcard, -, -, hZcard, -⟩ := lyons_unitary_four_fusion_and_centralizers hnonab hH S U hSU
  exact strong_embedding_sylow_sixty_four_center_four _ hemb S hcard hZcard

theorem lyons_unitary_four_recognition_from_strong_embedding
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : ∃ (H : Type) (_ : Group H) (S : Sylow 2 G) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2 := by
  obtain ⟨H, _, S, U, hH, hSU⟩ := h
  exact lyons_unitary_four_recognition_of_sylow hnonab S ⟨H, inferInstance, U, hH, hSU⟩

theorem lyons_unitary_four_recognition [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : ∃ (H : Type) (_ : Group H) (S : Sylow 2 G) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2 :=
  lyons_unitary_four_recognition_from_strong_embedding hnonab h

end CFSG.LyonsUnitaryFour
