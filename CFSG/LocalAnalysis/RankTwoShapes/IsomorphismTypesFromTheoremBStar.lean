module

public import CFSG.LocalAnalysis.RankTwoShapes.IsomorphismTypes
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Recognition.Main
public import CFSG.CharacterTheory.Semidihedral.RecognitionRemaining
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeStationaryCoverageProof

public section

namespace CFSG.RankTwoShapes

open CFSG.Assembly.LowTwoRank in
theorem rank_two_isomorphism_types_of_theoremBStar
    (hB : CFSG.Semidihedral.SimpleLayerFrontier.StationaryCoverageStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) :=
  rank_two_isomorphism_types_of_recognitions
    (CFSG.Semidihedral.RecognitionFromGaps.semidihedral_recognition_of_theoremBStar hB)
    (fun G _ _ _ hnonab hwr =>
      CFSG.Semidihedral.RecognitionFromGaps.wreathed_recognition_of_theoremBStar hB hSC G hnonab
        hwr)
    (fun _ _ _ _ hnonab h => CFSG.LyonsUnitaryFour.lyons_unitary_four_recognition hnonab h)
    G hnonab hrank

open CFSG.Assembly.LowTwoRank in
theorem rank_two_isomorphism_types_of_semidihedral_theoremBStar
    (hB : CFSG.Semidihedral.SimpleLayerFrontier.StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) :=
  rank_two_isomorphism_types_of_theoremBStar hB
    CFSG.Wreathed.OriginalAllPrime.stationaryCoverageStatement_holds G hnonab hrank

end CFSG.RankTwoShapes
