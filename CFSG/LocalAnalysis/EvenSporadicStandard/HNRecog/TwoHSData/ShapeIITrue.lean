module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIISpec2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrimes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import Certificates.Certificate26776

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

theorem nonempty_centralizer_mulEquiv_of_isConj {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({y} : Set G))) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact ⟨TwoHSData.centralizerMulEquiv (MulAut.conj c) x⟩

section Cert


theorem shapesIIOK_true : shapesIIOK = true := Certificates.certificate26776

private theorem shapesII_parts : shape3OK = true ∧ shape5AOK = true ∧ shape5BOK = true ∧
    shape5COK = true ∧ shape7OK = true := by
  have h := shapesIIOK_true
  simp only [shapesIIOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem table_three_P (hP : Nat.card ↥P1408 = 177408000) (t : ↥P1408) (ht : orderOf t = 3) :
    IsShapeCentralizerThree ↥(centralizer ({t} : Set ↥P1408)) := by
  obtain ⟨d, hd, hc⟩ := (primeFacts3 hP).2 t ht
  obtain rfl : d = fix3 := by simpa using hd
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hc
  exact IsShapeCentralizerThree.of_mulEquiv e
    (IsShapeCentralizerThree.of_mulEquiv (centralizerSubtypeEquiv P1408 (repP fix3)).symm
      (isShapeCentralizerThree_of_shape3OK shapesII_parts.1
        ((primeFacts3 hP).1 fix3 (by simp)).1))

theorem isShape_repP_five_C (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeCentralizerFiveC ↥(centralizer ({repP fix5C} : Set ↥P1408)) :=
  IsShapeCentralizerFiveC.of_mulEquiv (centralizerSubtypeEquiv P1408 (repP fix5C)).symm
    (isShapeCentralizerFiveC_of_shape5COK shapesII_parts.2.2.2.1 elemA_mul_self
      (ne_one_of_orderOf_eq_two twoHSBasic_spec.1) (fun g hg => elemA_comm hg)
      ((primeFacts5 hP).1 fix5C (by simp)).1)

theorem isShape_repP_five_B (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeCentralizerFiveB ↥(centralizer ({repP fix5B} : Set ↥P1408)) :=
  IsShapeCentralizerFiveB.of_mulEquiv (centralizerSubtypeEquiv P1408 (repP fix5B)).symm
    (isShapeCentralizerFiveB_of_shape5BOK shapesII_parts.2.2.1
      ((primeFacts5 hP).1 fix5B (by simp)).1)

theorem table_five_P (hP : Nat.card ↥P1408 = 177408000) (t : ↥P1408) (ht : orderOf t = 5) :
    IsShapeCentralizerFiveA ↥(centralizer ({t} : Set ↥P1408)) ∨
      IsShapeCentralizerFiveB ↥(centralizer ({t} : Set ↥P1408)) ∨
        IsShapeCentralizerFiveC ↥(centralizer ({t} : Set ↥P1408)) := by
  have hF := primeFacts5 hP
  obtain ⟨d, hd, hc⟩ := hF.2 t ht
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact Or.inl (IsShapeCentralizerFiveA.of_mulEquiv e
      (IsShapeCentralizerFiveA.of_mulEquiv (centralizerSubtypeEquiv P1408 (repP fix5A)).symm
        (isShapeCentralizerFiveA_of_shape5AOK shapesII_parts.2.1 (hF.1 fix5A (by simp)).1
          (hF.1 fix5A (by simp)).2)))
  · exact Or.inr (Or.inl (IsShapeCentralizerFiveB.of_mulEquiv e (isShape_repP_five_B hP)))
  · exact Or.inr (Or.inr (IsShapeCentralizerFiveC.of_mulEquiv e (isShape_repP_five_C hP)))

theorem table_seven_P (hP : Nat.card ↥P1408 = 177408000) (t : ↥P1408) (ht : orderOf t = 7) :
    IsShapeCentralizerSeven ↥(centralizer ({t} : Set ↥P1408)) := by
  have hF := primeFacts7 hP
  obtain ⟨d, hd, hc⟩ := hF.2 t ht
  obtain rfl : d = fix7 := by simpa using hd
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hc
  exact IsShapeCentralizerSeven.of_mulEquiv e
    (IsShapeCentralizerSeven.of_mulEquiv (centralizerSubtypeEquiv P1408 (repP fix7)).symm
      (isShapeCentralizerSeven_of_shape7OK shapesII_parts.2.2.2.2 elemA_mul_self
        (ne_one_of_orderOf_eq_two twoHSBasic_spec.1) (fun g hg => elemA_comm hg)
        (hF.1 fix7 (by simp)).1 (hF.1 fix7 (by simp)).2))

end Cert

end CFSG.EvenSporadicStandard.HNRecog
