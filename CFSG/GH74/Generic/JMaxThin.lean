module

public import CFSG.GH74.Generic.JMax

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

@[expose] def S_shapeCaseMaxNT
    (P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop) : Prop :=
  S_shapeCase (fun {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) =>
    ¬ GLS.HasTwoThinConfiguration G ∧ IsJMax x K ∧ P x K)

theorem S_shapeCaseMaxNT_of_S_shapeCaseMax
    {P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop}
    (h : S_shapeCaseMax @P) : S_shapeCaseMaxNT @P :=
  fun G _ _ hs hn hr hgen hK hnab hL x hx K hKc hG2 hP =>
    h G hs hn hr hgen hK hnab hL x hx K hKc hG2 hP.2

theorem S_shapeCaseMaxNT_of_S_shapeCase
    {P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop}
    (h : S_shapeCase @P) : S_shapeCaseMaxNT @P :=
  S_shapeCaseMaxNT_of_S_shapeCaseMax (S_shapeCaseMax_of_S_shapeCase h)

@[expose] def S_genericThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) → GLS.L2Meets G GLS.InG2 →
        GLS.HasTwoThinConfiguration G → Catalog G

theorem s_generic_of_shape_casesMaxNT
    (hF : GenericKnownFacts) (hT : S_genericThin)
    (h1 : S_shapeCaseMaxNT @ShapeS1) (h2 : S_shapeCaseMaxNT @ShapeS2)
    (h3 : S_shapeCaseMaxNT @ShapeS3) (h4 : S_shapeCaseMaxNT @ShapeS4)
    (h5 : S_shapeCaseMaxNT @ShapeS5) : S_generic' := by
  intro G _ _ hs hn hr hgen hK hnab hL hg
  by_cases hthin : GLS.HasTwoThinConfiguration G
  · exact hT G hs hn hr hgen hK hnab hL hg hthin
  obtain ⟨x₀, hx₀, K₀, hK₀c, hK₀G2⟩ := hg
  obtain ⟨x, K, hmax⟩ := exists_isJMax ⟨x₀, K₀, hx₀, hK₀c, hK₀G2⟩
  obtain ⟨hx, hKc, hG2⟩ := hmax.1
  rcases generic_shapes_of_inG2 hF hs hn hgen hK hx hG2 with h | h | h | h | h
  · exact h1 G hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, h⟩
  · exact h2 G hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, h⟩
  · exact h3 G hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, h⟩
  · exact h4 G hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, h⟩
  · exact h5 G hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, h⟩

end CFSG.GH74.Generic
