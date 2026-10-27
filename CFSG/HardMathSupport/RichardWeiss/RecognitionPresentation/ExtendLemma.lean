module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.OrderThreeClass
public import Certificates.Certificate134002

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation


theorem extendTree_ok :
    extendTree.okF [0, 1, 2] 3 extendRels :=
  Certificates.certificate134002.1

theorem extendTree_succs :
    ∀ t ∈ extendTree.succs, t ∈ extendSucc :=
  Certificates.certificate134002.2

variable {J : Type*} [Group J] {D : J → Prop}

theorem OrderThreeClass.extend_lemma (hD : OrderThreeClass D)
    {a b c d : J} (ha : D a) (hb : D b) (hc : D c) (hd : D d) (hab : (a * b) ^ 2 = 1)
    (hac : (a * c) ^ 2 = 1) (hbc : (b * c) ^ 2 = 1)
    (had : (a * d) ^ 2 = 1) :
    d ∈ Subgroup.closure {a, b, c} ∨ (b * d) ^ 2 = 1 ∨ (c * d) ^ 2 = 1 ∨
      (a⁻¹ * b * a * d) ^ 2 = 1 ∨ (a⁻¹ * c * a * d) ^ 2 = 1 ∨ (a * b * a⁻¹ * d) ^ 2 = 1 ∨
      (a * c * a⁻¹ * d) ^ 2 = 1 := by
  have hrels : ∀ r ∈ extendRels, evalW ![a, b, c, d] r = 1 := by
    intro r hr
    simp only [extendRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [evalW_pow, evalW_mul, evalW_of, hD.cube _ ha, hD.cube _ hb, hD.cube _ hc,
        hD.cube _ hd, hab, hac, hbc, had]
  rcases hD.tree_sound ha hb hc hd extendTree extendRels hrels extendTree_ok with h | ⟨t, ht, h⟩
  · exact Or.inl h
  · have hm := extendTree_succs t ht
    simp only [extendSucc, List.mem_cons, List.not_mem_nil, or_false] at hm
    right
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [evalW_cdesc_elt] at h <;>
      simp only [evalW_letter, evalW_one, Bool.false_eq_true, ↓reduceIte, inv_inv, inv_one, one_mul, mul_one,
        vec4_zero, vec4_one, vec4_two] at h <;>
      tauto

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
