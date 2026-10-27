module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.LocalAnalysis.ComponentInitial.CLSSmallReeModelInvolutionsInner

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup CFSG.LieType.Ree


theorem oneClass_ree {L : Type} [Group L] {p f : ℕ}
    (h : Blueprint.ReeTitsModel L .twistedG2 p f) : OneClass L := by
  obtain ⟨-, -, hp, -, hiso⟩ := small_Ree_model_Schreier L p f h
  obtain ⟨-, a, hfa, K, _, _, hK, he⟩ := h
  subst hp
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK he
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨w₀, hw₀, -⟩ := LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  have hcls := (Walter.Ree.Model.small_Ree_prime_field_involution_fusion a K hK' w₀ hw₀).2.2.2.2.2
  exact (oneClass_of_rep hcls).of_mulEquiv E

theorem ree : CF23InnerFusionFor fun Y _ =>
    ∃ m : ℕ, 1 ≤ m ∧ Blueprint.LieModel Y .twistedG2 0 3 (2 * m + 1) := by
  intro G _ _ N hN hC hY α J hα hJN hJα _ _ _ hZ _
  have := hN
  obtain ⟨m, -, hL⟩ := hY
  have hR : Blueprint.ReeTitsModel ↥N .twistedG2 3 (2 * m + 1) := by
    rcases hL with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact h
    · exact absurd ht (by decide)
  have hαN : α ∈ N := mem_of_inv_inner hC hα fun φ hφ =>
    LocalAnalysis.ComponentInitial.small_Ree_model_involutions_inner ↥N 3 (2 * m + 1) hR φ hφ
  exact concl_of_coset hα hJN hJα hZ (coset_of_inner hα hαN (oneClass_ree hR))

end CFSG.ComponentClassification.GSThmB.CF23I
