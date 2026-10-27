module

public import CFSG.GH74.RouteRefine
public import CFSG.GH74.Generic.ComponentShapes

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

@[expose] def S_shapeCase
    (P : ∀ {G : Type} [Group G] (x : G), Subgroup (CentralizerBar x) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
      (∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥) →
      ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → GLS.InG2 ↥K →
        P x K → Catalog G

theorem s_generic_of_shape_cases
    (hF : GenericKnownFacts)
    (h1 : S_shapeCase @ShapeS1) (h2 : S_shapeCase @ShapeS2) (h3 : S_shapeCase @ShapeS3)
    (h4 : S_shapeCase @ShapeS4) (h5 : S_shapeCase @ShapeS5) : S_generic' := by
  intro G _ _ hs hn hr hgen hK hnab hL hg
  obtain ⟨x, hx, K, hKc, hG2, hsh⟩ := generic_shapes_of_L2Meets hF hs hn hgen hK hg
  rcases hsh with h | h | h | h | h
  · exact h1 G hs hn hr hgen hK hnab hL x hx K hKc hG2 h
  · exact h2 G hs hn hr hgen hK hnab hL x hx K hKc hG2 h
  · exact h3 G hs hn hr hgen hK hnab hL x hx K hKc hG2 h
  · exact h4 G hs hn hr hgen hK hnab hL x hx K hKc hG2 h
  · exact h5 G hs hn hr hgen hK hnab hL x hx K hKc hG2 h

end CFSG.GH74.Generic
