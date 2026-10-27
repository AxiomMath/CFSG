module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def D1At (G : Type) [Group G] [Finite G] (q : ℕ) : Prop :=
  ∀ (Q : Sylow q G) (M : Subgroup G), GLBIsMaxTwoLocal M → GLBWeakCore q (Q : Subgroup G) ≤ M →
    ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ Open.pRank q (H ⊓ M) → H ≤ M

theorem false_of_guestPrime {G : Type} [Group G] [Finite G] (hpre : GLBPreuniqueness G) {q : ℕ}
    (hq : q ∈ GLBBetaFour G) (hD1 : D1At G q) {M H : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hH : GLBIsMaxTwoLocal H) (hHM : ¬ H ≤ M) (hrank : 3 ≤ Open.pRank q (H ⊓ M)) : False := by
  have hqp : q.Prime := hq.1
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained q hqp (H ⊓ M)
  have hE3 : ∀ K : Subgroup G, E ≤ K → 3 ≤ Open.pRank q K := fun K hEK =>
    (hrank.trans (le_csSup (pRank_bddAbove q hqp E) ⟨E, le_rfl, hEel, hEcard⟩)).trans
      (pRank_mono q hqp hEK)
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hEcard).exists_le_sylow
  obtain ⟨L, hL, hWL⟩ := (hpre q hq).2 Q
  obtain ⟨Mq, hLMq, hMq⟩ := exists_maximal_twoLocal hL
  have hWMq : GLBWeakCore q (Q : Subgroup G) ≤ Mq := hWL.trans hLMq
  have hEMq : E ≤ Mq :=
    hEQ.trans ((subgroup_le_weakCore_of_rank q hqp (Q : Subgroup G) (hE3 _ hEQ)).trans hWMq)
  have hHMq : H ≤ Mq := hD1 Q Mq hMq hWMq H hH.1 (hE3 _ (le_inf (hE.trans inf_le_left) hEMq))
  have hHeq : Mq = H := hH.2 Mq hMq.1 hHMq
  subst hHeq
  have hMH : M ≤ Mq :=
    hD1 Q Mq hMq hWMq M hM.1 (hE3 _ (le_inf (hE.trans inf_le_right) (hE.trans inf_le_left)))
  exact hHM (hM.2 Mq hMq.1 hMH).le

end CFSG.AGLEmbedding
