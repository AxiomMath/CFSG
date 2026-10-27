module

public import CFSG.GH74.Generic.ComponentBranches
public import CFSG.GH74.Generic.Sections

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup

theorem generic_shapes_of_inG2
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hG2 : InG2 ↥K) :
    GenericShape x K := by
  have hset := Setup.of_inG2 hG2
  have hGH := ghList_of_quasisimple hs hn hK hx hset.quasisimple
  rcases hGH with ⟨n, hn7, hn11, ⟨e⟩⟩ | hsp | ⟨p, f, hp, hf, hL⟩
  · exact shape_of_alt hF hgen hx hset hn7 hn11 e
  · rcases hsp with h | h | h | h | h | h | h | h | h
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_M11 hset.isSimple h)
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_M12 hset.isSimple h)
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_M22 hset.isSimple h)
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_M23 hset.isSimple h)
    · exact shape_of_J1 hF hx hset h
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_J2 hset.isSimple h)
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_J3 hset.isSimple h)
    · exact shape_of_McL hF hgen hx hset h
    · exact shape_of_Ly hF hgen hx hset h
  · rcases hL with ⟨hp2, h | h | h | h | h | h⟩ | ⟨hp2, -, h⟩ | ⟨hp2, -, h⟩ | ⟨hq, h⟩ | ⟨hq, h⟩ |
        h | ⟨-, h | h | h | h | h⟩
    · exact shape_of_psl2 hF hgen hx hset hp hp2 h
    · exact shape_of_psl3 hF hgen hx hset hp hp2 h
    · exact shape_of_psu3 hF hgen hx hset hp hp2 h
    · exact shape_of_psp4 hF hgen hx hset hp hp2 h
    · exact shape_of_g2 hF hgen hx hset hp hp2 h hf
    · exact shape_of_3D4 hF hgen hx hset hp hp2 h
    · exact shape_of_psl4 hF hgen hx hset hp hp2 h
    · exact shape_of_psu4 hF hgen hx hset hp hp2 h
    · exact shape_of_psl5 hF hgen hx hset hp hq h
    · exact shape_of_psu5 hF hgen hx hset hp hq h
    · exact shape_of_ree hF hx hset h
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_even hset.isSimple (Or.inl h))
    · exact shape_of_simpleInC2 hgen hx hset (simpleInC2_of_even hset.isSimple (Or.inr (Or.inl h)))
    · exact shape_of_simpleInC2 hgen hx hset
        (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inl h))))
    · exact shape_of_simpleInC2 hgen hx hset
        (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact shape_of_simpleInC2 hgen hx hset
        (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem generic_component_shapes
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (_hKc : IsComponent K)
    (hG2 : InG2 ↥K) : GenericShape x K :=
  generic_shapes_of_inG2 hF hs hn hgen hK hx hG2

theorem generic_shapes_of_L2Meets
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G)
    (h : L2Meets G InG2) :
    ∃ x : G, orderOf x = 2 ∧ ∃ K : Subgroup (CentralizerBar x), IsComponent K ∧ InG2 ↥K ∧
      GenericShape x K := by
  obtain ⟨x, hx, K, hKc, hG2⟩ := h
  exact ⟨x, hx, K, hKc, hG2, generic_shapes_of_inG2 hF hs hn hgen hK hx hG2⟩

end CFSG.GH74.Generic
