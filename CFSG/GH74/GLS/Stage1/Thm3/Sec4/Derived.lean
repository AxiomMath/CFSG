module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem ivk_1_2f_lifted_of_II4 (h44 : II4_44) (hAut : II4_Aut) : IVK_1_2f_lifted := by
  unfold IVK_1_2f_lifted
  intro G _ _ z S K₁ K₂ h K hK y _ hyn hord hnf
  have hKc : K = K₁ ∨ K = K₂ := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hK
  have hQ := h44 G h.simple z h.orderOf_z K (h.comp_isPCompIn hKc) (h.comp_pRank hKc)
  have hw : y * y ∈ normalizer (K : Set G) := mul_mem hyn hyn
  have hw2 : (y * y) * (y * y) = 1 := mul_self_eq_one_of_orderOf_eq_two hord
  have hD := ((hAut (↥K ⧸ pPrimeCore 2 ↥K) hQ).2.2 (phi K (y * y) hw)
    (phi_mul_self K hw hw2)).2
  by_contra hno
  have hninn : phi K (y * y) hw ∉ innOf (Hat K) := fun hmem =>
    hno ((phi_mem_inn_iff K hw).1 hmem)
  have hnfa : ¬ IsFAutomorphism (Hat K) (phi K (y * y) hw) := fun hf => hnf ⟨hw, hf⟩
  exact hD hninn hnfa (phi K y hyn) (phi_mul K hyn hyn).symm

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
