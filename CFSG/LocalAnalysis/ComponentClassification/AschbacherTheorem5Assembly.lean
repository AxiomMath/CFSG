module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5EndGame
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5CenterReduction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Final
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoGeneral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineAssembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalResults
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchur
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFactsAssembly
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalL1Six

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

theorem sectionSixInputs_of (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (h48 : AschbacherTheorem3.Theorem48Statement) : SectionSixInputs where
  theorem_2_part_two := fun Q htight hodd =>
    theorem_2_part_two CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      benderDoubleCoverRigidity Q htight hodd
  strongly_embedded_solvable := strongly_embedded_solvable
  lemma_3_8 := fun A U hA hUA hU h => AschbacherKnownGroup.lemma_3_8 hK A U hA hUA hU h
  lemma_4_9 := AschbacherTheorem3.lemma_4_9_of_theorem_4_8 h48
  knownGroups := hK

theorem sectionSevenBase_of (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (h48 : AschbacherTheorem3.Theorem48Statement)
    (h64 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
      {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
      Counterexample G D r Abar → ∀ g : G,
        rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G) →
        ∀ U : Subgroup G, U ≤ Subgroup.normalizer (D : Set G) →
          AschbacherKnownGroup.IsFourGroup U →
          ¬ ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
            rightConjugate (Subgroup.normalizer (D : Set G)) g) :
    SectionSevenBase where
  lemma_6_3 := fun hC i j =>
    lemma_6_3 (AschbacherTheorem3.theorem_3_of_theorem_4_8 h48) (sectionSixInputs_of hK h48)
      hC i j
  theorem_6_4 := h64
  theorem_3_3 := fun H z hz hH huniq =>
    theorem_3_3 CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      benderDoubleCoverRigidity H z hz hH huniq
  lemma_3_4 := fun S A₁ A₂ =>
    lemma_3_4_trichotomy CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      benderDoubleCoverRigidity S A₁ A₂
  theorem_3 := AschbacherTheorem3.theorem_3_of_theorem_4_8 h48
  knownGroups := hK

theorem sectionSevenInputs_of (hbase : SectionSevenBase)
    (h74 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
      {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
      Counterexample G D r Abar → ∀ t g : G, t ∈ Subgroup.normalizer (D : Set G) →
        orderOf t = 2 → g ∉ Subgroup.normalizer (D : Set G) →
        (∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
          (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) →
        (∀ k : Fin r, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
          aschbacherThm5Preimage D (Abar k)) →
        ∀ k : Fin r, IsSimpleGroup (Abar k) ∧ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) :
    SectionSevenInputs :=
  { hbase with
    lemma_7_4_dihedral := h74
    lemma_8_2 := lemma_8_2_holds hbase }

theorem sectionSevenInputs_of_caseD (hbase : SectionSevenBase) (hd : SevenFour.CaseDImpossible) :
    SectionSevenInputs :=
  sectionSevenInputs_of hbase (SevenFour.lemma_7_4_dihedral_holds hbase hd)

theorem conclusion_of_sectionSevenInputs (hin : SectionSevenInputs) :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar :=
  reduction_to_trivial_center fun _ _ _ _ _ _ hC => counterexample_false hin hC

theorem theorem_6_4_of_inputs (hG : CFSG.Goldschmidt.TopStatement)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hK3 : AschbacherTheorem3.Theorem3KnownGroupFacts)
    (h48 : AschbacherTheorem3.Theorem48Statement)
    {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hC : Counterexample G D r Abar)
    (g : G) (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠
      Subgroup.normalizer (D : Set G))
    (U : Subgroup G) (hUH : U ≤ Subgroup.normalizer (D : Set G))
    (hU : AschbacherKnownGroup.IsFourGroup U) :
    ¬ ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  have h3 := AschbacherTheorem3.theorem_3_of_theorem_4_8 h48
  have hglob : SectionSixGlobalInputs :=
    { theorem_3 := h3
      lemma_4_6 := AschbacherTheorem3.lemma_4_6 hG hK3
      theorem_4_8 := h48
      goldschmidt := hG
      goldschmidt_type_automorphisms := hK3.goldschmidt_type_automorphisms }
  have hloc := sectionSixLocalResults_of_inputs h3 (sectionSixInputs_of hK h48)
  exact (deltaConjugates_eq_empty_iff _).mp (theorem_6_4 hglob hloc hC) g hg U hUH hU.1 hU.2

theorem conclusion_of_inputs (hG : CFSG.Goldschmidt.TopStatement)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hK3 : AschbacherTheorem3.Theorem3KnownGroupFacts)
    (h48 : AschbacherTheorem3.Theorem48Statement) :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar :=
  let hbase := sectionSevenBase_of hK h48
    (fun hC g hg U hUH hU => theorem_6_4_of_inputs hG hK hK3 h48 hC g hg U hUH hU)
  conclusion_of_sectionSevenInputs
    (sectionSevenInputs_of hbase (SevenFour.lemma_7_4_dihedral_holds_of_base hbase))

theorem conclusion_of_goldschmidt (hG : CFSG.Goldschmidt.TopStatement)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar :=
  have hK3 := CFSG.ComponentClassification.WalterSchur.theorem3KnownGroupFacts_holds
  conclusion_of_inputs hG hK hK3
    (AschbacherTheorem3.theorem_4_8_of_F2 hG
      CFSG.ComponentClassification.WalterSchur.walter_schur_two_part_holds
      (AschbacherTheorem3.lemma_4_6 hG hK3))

theorem conclusion_of_topStatement (hG : CFSG.Goldschmidt.TopStatement) :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar :=
  conclusion_of_goldschmidt hG AschbacherKnownGroup.knownGroupFacts_holds

end CFSG.ComponentClassification.AschbacherTheorem5
