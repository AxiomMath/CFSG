module

public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly CFSG.StandardType

@[expose] def DerivedLab (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2der ∨ lab.tag = .twF4der

abbrev CAll : LargeEvenLabel → LargeEvenRawCont → Prop :=
  CFSG.StandardType.Canonical.LargeEvenLabelAll

theorem rawDatum_iff_legacy {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ DerivedLab lab) (Q : LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum lab Q ↔ CFSG.StandardType.LargeEvenRawDatum lab Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case G2der => exact absurd (Or.inl rfl) hd
  case twF4der => exact absurd (Or.inr rfl) hd
  case twF4 =>
    obtain ⟨-, -, -, h3⟩ := hlab
    have h3' : 3 ≤ n := h3
    have ha : (n - 1) / 2 ≠ 0 := by omega
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.StandardType.LargeEvenRawDatum,
      LargeEvenRecipeTwF4Inherited, LargeEvenRecipeTwF4]
    simp only [if_neg ha]
  all_goals exact Iff.rfl

theorem canonAll_iff_legacyAll {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ DerivedLab lab) (P : LargeEvenRawCont) :
    CAll lab P ↔ CFSG.StandardType.LargeEvenLabelAll lab P := by
  unfold CAll CFSG.StandardType.Canonical.LargeEvenLabelAll CFSG.StandardType.LargeEvenLabelAll
  refine forall_congr' fun Q => ?_
  rw [rawDatum_iff_legacy hlab hd, rawDatum_iff_legacy hlab hd]

theorem CAll.mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : CAll lab P) : CAll lab P' := fun Q hQ =>
  Canonical.largeEvenRawDatum_mono (fun R _ I F ⟨hq, hp⟩ => ⟨hq, hPP' R I F hp⟩) (h Q hQ)

theorem CAll.and {lab : LargeEvenLabel} {P P' : LargeEvenRawCont} (h : CAll lab P)
    (h' : CAll lab P') : CAll lab fun R _ I F => P R I F ∧ P' R I F := fun Q hQ =>
  Canonical.largeEvenRawDatum_mono (fun R _ I F ⟨⟨hq, hp⟩, hp'⟩ => ⟨hq, hp, hp'⟩) (h' _ (h Q hQ))

theorem canonRawDatum_or {lab : LargeEvenLabel} {Q₁ Q₂ : LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => Q₁ R I F ∨ Q₂ R I F) :
    CFSG.Assembly.LargeEvenRawDatum lab Q₁ ∨ CFSG.Assembly.LargeEvenRawDatum lab Q₂ := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, b, c, hbc, hq⟩, Or.inr ⟨K, i1, i2, hK, b, c, hbc, hq⟩])
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, hq⟩, Or.inr ⟨K, i1, i2, hK, hq⟩])

theorem canonAll_simple_of_markedModel
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {P : LargeEvenRawCont}
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → MarkedModel lab R → P R I F) :
    CAll lab (LargeEvenSimpleGuard P) := by
  intro Q hQ
  have hor : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F =>
      (Q R I F ∧ IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) ∨
        (Q R I F ∧ ¬ (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a)) := by
    refine Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ?_) hQ
    by_cases hs : IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a
    · exact Or.inl ⟨hq, hs⟩
    · exact Or.inr ⟨hq, hs⟩
  rcases canonRawDatum_or hor with h1 | h2
  · exact Canonical.largeEvenRawDatum_imp hlab (fun _ _ _ _ hq => hq.2.2)
      (fun R _ I F hq hm => ⟨hq.1, fun hs hna => h R I F hs hna hm⟩) h1
  · exact Canonical.largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq.1, fun hs hna => absurd ⟨hs, hna⟩ hq.2⟩) h2

theorem canon_marking_and_labelAll_simple {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → CAll lab (LargeEvenSimpleGuard P'))
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' := hall lab hlab _ hraw
  refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

end MI

end CFSG.LocalAnalysis.GLTheoremA
