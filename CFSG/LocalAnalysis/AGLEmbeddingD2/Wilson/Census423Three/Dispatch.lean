module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LinUniGlue

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem isSimpleGroup_of_isQuasisimple_center {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  obtain ⟨-, hs, -⟩ := hq
  have e : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact MulEquiv.isSimpleGroup e

@[expose] def G2Census423 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (X : Type) [Group X] [Finite X],
    Blueprint.ChevalleyExceptionalModel X .G2 p 1 → CFSG.IsQuasisimple X →
      Subgroup.center X = ⊥ → Census423 X

theorem k423Inner46Three_of_g2 (hG2 : G2Census423) : K423Inner46Three := by
  intro X _ _ h hq hZ _
  obtain ⟨p, hp, h3, hcase⟩ := h
  have : IsSimpleGroup X := isSimpleGroup_of_isQuasisimple_center hq hZ
  rcases hcase with hm | he | ⟨h1, he⟩ | ⟨h2, he⟩
  · exact hG2 p h3 X hm hq hZ
  · obtain ⟨e⟩ := he
    exact census423_of_projSp h3 hZ e
  · obtain ⟨e⟩ := he
    exact census423_of_projSU_four h3 h1 hZ e
  · obtain ⟨e⟩ := he
    exact census423_of_projSL_four h3 h2 hZ e

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
