module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.OrderThreeClass
public import Certificates.Certificate134001

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation


theorem starTree_ok : starTree.okF [0, 1, 2] 3 starRels :=
  Certificates.certificate134001.1

theorem starTree_succs :
    ∀ t ∈ starTree.succs, t = ⟨(2, true), 1⟩ :=
  Certificates.certificate134001.2

variable {J : Type*} [Group J] {D : J → Prop}

theorem OrderThreeClass.star_lemma (hD : OrderThreeClass D)
    {a b c d : J} (ha : D a) (hb : D b) (hc : D c) (hd : D d) (hab : (a * b) ^ 2 = 1)
    (hac : (a * c) ^ 2 = 1) (hbc : (b * c) ^ 2 = 1)
    (had : (a * d) ^ 2 = 1) (hbd : (b * d) ^ 2 = 1) :
    d ∈ Subgroup.closure {a, b, c} ∨ (c * d) ^ 2 = 1 := by
  have hrels : ∀ r ∈ starRels, evalW ![a, b, c, d] r = 1 := by
    intro r hr
    simp only [starRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [evalW_pow, evalW_mul, evalW_of, hD.cube _ ha, hD.cube _ hb, hD.cube _ hc,
        hD.cube _ hd, hab, hac, hbc, had, hbd]
  rcases hD.tree_sound ha hb hc hd starTree starRels hrels starTree_ok with h | ⟨t, ht, h⟩
  · exact Or.inl h
  · obtain rfl := starTree_succs t ht
    right
    rw [evalW_cdesc_elt] at h
    simpa only [evalW_letter, evalW_one, Bool.false_eq_true, ↓reduceIte, inv_inv, inv_one, one_mul, mul_one,
      vec4_zero, vec4_one, vec4_two, vec4_three] using h

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
