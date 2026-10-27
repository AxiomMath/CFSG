module

public import CFSG.HardMathSupport.Foote.E27.Q2IndexUni
public import CFSG.HardMathSupport.Foote.E27.LieTwo.IndexOrth
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.AssemblyIn

public section

namespace CFSG.HardMathSupport.Foote.E27

open TauCeti CFSG.HardMathSupport.Malle.E27Lie

theorem innerLeaf_qTwo :
    InnerLeaf IdxQTwo := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨di, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hq, hr3, hr8⟩ | ⟨r, q, rfl, hq, hr⟩ | ⟨r, q, rfl, hq, hr⟩ |
    ⟨r, q, rfl, hq, hr⟩
  · obtain ⟨hp, hf⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
    exact h.false_of_typeTwistedA_two hz hv e hp hf ⟨hr3, hr8⟩
  · obtain ⟨hp, -⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
    rcases hr with rfl | rfl
    · exact h.false_of_typeB_three_two hv e hp hq
    · exact h.false_of_typeB_four_two hz hv e hp hq
  · obtain ⟨hp, -⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
    exact h.false_of_typeD_two hz hv e hp hq hr
  · obtain ⟨hp, -⟩ := prime_pow_eq_two q.prime_p q.exponent_pos hq
    exact h.false_of_typeTwistedD_two hz hv e hp hq hr

end CFSG.HardMathSupport.Foote.E27
