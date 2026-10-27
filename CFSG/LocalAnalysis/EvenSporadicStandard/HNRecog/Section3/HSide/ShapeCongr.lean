module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {X X' : Type*} [Group X] [Group X']

theorem IsShapeZ2TimesSym.of_mulEquiv {n : ℕ} (e : X ≃* X') (h : IsShapeZ2TimesSym n X) :
    IsShapeZ2TimesSym n X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeD8TimesS3.of_mulEquiv (e : X ≃* X') (h : IsShapeD8TimesS3 X) : IsShapeD8TimesS3 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeTwoTwoTimesD8.of_mulEquiv (e : X ≃* X') (h : IsShapeTwoTwoTimesD8 X) :
    IsShapeTwoTwoTimesD8 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeZ2TimesD8.of_mulEquiv (e : X ≃* X') (h : IsShapeZ2TimesD8 X) : IsShapeZ2TimesD8 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeZ2TimesD10.of_mulEquiv (e : X ≃* X') (h : IsShapeZ2TimesD10 X) :
    IsShapeZ2TimesD10 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeU35.of_mulEquiv (e : X ≃* X') (h : IsShapeU35 X) : IsShapeU35 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsShapeTwoTwoTimesA5.of_mulEquiv (e : X ≃* X') (h : IsShapeTwoTwoTimesA5 X) :
    IsShapeTwoTwoTimesA5 X' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
