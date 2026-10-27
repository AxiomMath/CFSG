module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem rk2_rawDatum_mono {lab : GLALabel} {Q Q' : CFSG.Assembly.LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : GLARawDatum lab Q) : GLARawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hQQ' _ _ _ hq⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hQQ' _ _ _ hq⟩)

theorem rk2_rawDatum_exists {lab : GLALabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (h : GLARawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem rk2_marking_mono {X : Type} [Group X] {P P' : GLAMarkProp X}
    (hPP' : ∀ (lab : GLALabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F θ)
    (h : GLAMarking X P) : GLAMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, rk2_rawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hθ⟩

theorem rk2_marking_and_labelAll {X : Type} [Group X] {P : GLAMarkProp X}
    {P' : GLALabel → CFSG.Assembly.LargeEvenRawCont}
    (hall : ∀ lab, GLAInLambda2 lab → Rk2LabelAll lab (P' lab)) (h : GLAMarking X P) :
    GLAMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' lab R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, rk2_rawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP'⟩

theorem rk2_exists_label {X : Type} [Group X] {P : GLAMarkProp X} (h : GLAMarking X P) :
    ∃ lab : GLALabel, GLAInLambda2 lab ∧ Rk2IsLabel X lab := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨lab, hlab, hX, lab, hlab, rk2_rawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA
