module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneMain
public import CFSG.CharacterTheory.Semidihedral.ParameterFiveRecognition
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranch
public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryBranch
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValue
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivial

public section

namespace CFSG.Semidihedral.RecognitionFromGaps

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.SimpleLayerFrontier

theorem semidihedral_recognition_of_remaining
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement) (hD : UnitaryBranch.DValueStatement) :
    CFSG.Wreathed.RecognitionFromGaps.SemidihedralRecognitionStatement :=
  fun G _ _ _ hnonab hsd =>
    semidihedral_recognition_of_local_theorems hB FieldFactorOne.field_factor_one hA
      (UnitaryBranch.unitary_branch_of_d_value hD) ParameterFive.parameterFiveRecognition G
      hnonab hsd

theorem wreathed_recognition_of_remaining
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement) (hD : UnitaryBranch.DValueStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (hDW : CFSG.Wreathed.SameFieldUnitary.DValueStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hwr : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) :=
  CFSG.Wreathed.RecognitionFromGaps.wreathed_recognition_of_local_theorems
    (semidihedral_recognition_of_remaining hB hA hD) hSC
    (CFSG.Wreathed.SameFieldUnitary.unitaryBranch_of_dValue hDW) G hnonab hwr

theorem semidihedral_catalogue_of_remaining
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement) (hD : UnitaryBranch.DValueStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hsd : ∃ n : ℕ, 4 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* SemidihedralGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) ∨
    Nonempty (G ≃* CFSG.Open.M11) :=
  semidihedral_catalogue_of_local_theorems hB FieldFactorOne.field_factor_one hA
    (UnitaryBranch.unitary_branch_of_d_value hD) ParameterFive.parameterFiveRecognition G hnonab
    P hsd

theorem wreathed_catalogue_of_remaining
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement) (hD : UnitaryBranch.DValueStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (hDW : CFSG.Wreathed.SameFieldUnitary.DValueStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hwr : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) :=
  CFSG.Wreathed.RecognitionFromGaps.wreathed_catalogue_of_local_theorems
    (semidihedral_recognition_of_remaining hB hA hD) hSC
    (CFSG.Wreathed.SameFieldUnitary.unitaryBranch_of_dValue hDW) G hnonab P hwr

theorem dValueStatement_holds
    : UnitaryBranch.DValueStatement :=
  UnitaryBranch.dValue_of_centralizerCharacterTrivial
    fun G _ _ _ => FieldFactorOne.simple_centralizer_linear_character_trivial G

theorem unitaryBranchStatement_holds
    : UnitaryBranchStatement :=
  UnitaryBranch.unitary_branch_of_d_value dValueStatement_holds

theorem semidihedral_recognition_of_two
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement) :
    CFSG.Wreathed.RecognitionFromGaps.SemidihedralRecognitionStatement :=
  semidihedral_recognition_of_remaining hB hA dValueStatement_holds

theorem wreathed_recognition_of_three
    (hB : StationaryCoverageStatement)
    (hA : FixedCoreNontrivialStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hwr : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) :=
  CFSG.Wreathed.RecognitionFromGaps.wreathed_recognition_of_local_theorems
    (semidihedral_recognition_of_two hB hA) hSC CFSG.Wreathed.SameFieldUnitary.unitaryBranch G
    hnonab hwr

theorem semidihedral_recognition_of_theoremBStar
    (hB : StationaryCoverageStatement) :
    CFSG.Wreathed.RecognitionFromGaps.SemidihedralRecognitionStatement :=
  semidihedral_recognition_of_two hB FixedCoreNontrivial.fixedCoreNontrivial

theorem semidihedral_catalogue_of_theoremBStar
    (hB : StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hsd : ∃ n : ℕ, 4 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* SemidihedralGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) ∨
    Nonempty (G ≃* CFSG.Open.M11) :=
  semidihedral_catalogue_of_remaining hB FixedCoreNontrivial.fixedCoreNontrivial
    dValueStatement_holds G hnonab P hsd

theorem wreathed_recognition_of_theoremBStar
    (hB : StationaryCoverageStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hwr : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) :=
  wreathed_recognition_of_three hB FixedCoreNontrivial.fixedCoreNontrivial hSC G hnonab hwr

theorem wreathed_catalogue_of_theoremBStar
    (hB : StationaryCoverageStatement)
    (hSC : CFSG.Wreathed.RecognitionFromGaps.StationaryCoverageStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hwr : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* CFSG.Open.PSU3 p k)) :=
  CFSG.Wreathed.RecognitionFromGaps.wreathed_catalogue_of_local_theorems
    (semidihedral_recognition_of_theoremBStar hB) hSC CFSG.Wreathed.SameFieldUnitary.unitaryBranch
    G hnonab P hwr

end CFSG.Semidihedral.RecognitionFromGaps
