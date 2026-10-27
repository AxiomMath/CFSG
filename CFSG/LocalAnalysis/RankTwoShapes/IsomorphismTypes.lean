module

public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
public import CFSG.Milestones.LR_dihedral_simple_recognition
public import CFSG.Open.StatedDefs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.RankTwoShapes

open CFSG.Assembly.LowTwoRank in
theorem rank_two_isomorphism_types_of_recognitions
    (hsd : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (S : Sylow 2 G) (n : ℕ), 4 ≤ n ∧
        Nonempty ((S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f) ∨
      Nonempty (G ≃* CFSG.Open.StatedM11))
    (hwr : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
        Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          CFSG.Open.StatedClassicalModel G .PSU 3 p f))
    (hlyons : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      (∃ (H : Type) (_ : Group H) (S : Sylow 2 G) (U : Sylow 2 H),
        CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
          Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  rcases rank_two_sylow_shapes hnonab hrank S with
    ⟨n, hn, hS⟩ | ⟨n, hn, hS⟩ | ⟨n, hn, hS⟩ | ⟨H, hH, U, hmodel, he⟩
  · rcases CFSG.Milestones.lr_dihedral_simple_recognition G hnonab S n hn hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hsd G hnonab ⟨S, n, hn, hS⟩ with
      ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, -, hm⟩ | h
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases hwr G hnonab ⟨S, n, hn, hS⟩ with
      ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, -, hm⟩
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hlyons G hnonab ⟨H, hH, S, U, hmodel, he⟩))))

end CFSG.RankTwoShapes
