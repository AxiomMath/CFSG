module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley


theorem oddLocalWitness_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (hm : ChevalleyExceptionalModel S .trialityD4 2 f) : OddLocalWitness S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, z, -, hx, hz, hxz, -⟩ :=
    even_Chevalley_exceptional_real_three_element_centralizing_involution S .trialityD4 f hm
  refine ⟨3, Nat.prime_three, by norm_num, ?_, ?_⟩
  · obtain ⟨-, hm'⟩ := hm
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted hf hm'
    have : CharP K 2 := charP_two_of_natCard (by rw [hK, ← pow_mul])
    have h3 : ∀ c, σ (σ (σ c)) = c := fun c => by
      have := Fintype.ofFinite K
      have hord : TwistTag.D4.order = 3 := rfl
      have hc : Fintype.card K = 2 ^ f * (2 ^ f * 2 ^ f) := by
        rw [← Nat.card_eq_fintype_card, hK, hord]
        ring
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, ← hc, FiniteField.pow_card]
    have : Finite (graphFixedRootGroup .D4 K σ) := Finite.of_equiv S e.symm.toEquiv
    obtain ⟨-, E, hE, hEc⟩ := even_triality_commuting_rank_one_product_and_elementary_nine K σ h3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e.symm]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hE) (by rw [hEc]; norm_num)
  · have hne : Subgroup.zpowers z ≠ ⊥ := fun h => by
      have h1 : z = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers z)
      rw [h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    exact one_le_localRank_of_mem_normalizer (by norm_num) hne
      (isPGroup_zpowers_of_sq (by rw [← hz]; exact pow_orderOf_eq_one z))
      (mem_normalizer_zpowers hxz) hx

end CFSG.SectionRank.QTK
