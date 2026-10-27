module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem c25_small_case {X K B : Subgroup G} (hK : GLAPComponent 3 X K) (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hA : Nat.card (c25Img K B) ≤ 3) :
    ∃ E : Subgroup G, E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E ∧
      ∃ J : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set G)) J ∧
        K ≤ J ⊔ GLAPPrimeCoreOf 3 K := by
  have h3 : Nat.card (c25Img K B) ≤ 3 * Nat.card (⊥ : Subgroup (MulAut (barOf 3 K))) := by
    rw [Subgroup.card_bot]
    omega
  obtain ⟨E, hEB, hES, hrk⟩ := c25_exists_sub hBel hBN (S := ⊥) bot_le h3
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := hEB.trans hBN
  have hE3 : IsPGroup 3 ↥E := c25_isPGroup_of_elemAbelian (c25_isElemAbelian_mono hEB hBel)
  have hEd : E ≤ dQ K := by
    intro e he
    refine (LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K)
      ⟨e, hEN he⟩).2 ?_
    have : barAut 3 K ⟨e, hEN he⟩ ∈ c25Img K E :=
      ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    rw [hES, Subgroup.mem_bot] at this
    exact this
  obtain ⟨J, hJ, hKJ, -, -⟩ := coverStmt G X K E hK hE3 hEd
  exact ⟨E, hEB, hrk, J, hJ, hKJ⟩

end CFSG.HardMathSupport.Solomon.Coordinator
