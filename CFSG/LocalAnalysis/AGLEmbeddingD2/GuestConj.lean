module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.LocalAnalysis.AGLEmbedding.GuestPrime
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isTwoLocal_map_conj {H : Subgroup G} (hH : IsTwoLocal H) (g : G) :
    IsTwoLocal (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨T, hT, hT2, rfl⟩ := hH
  refine ⟨T.map (MulAut.conj g).toMonoidHom, ?_, hT2.map _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  · exact Subgroup.map_equiv_normalizer_eq T (MulAut.conj g)

theorem exists_weakCore_le_of_three_le_pRank (hpre : GLBPreuniqueness G) {q : ℕ}
    (hq : q ∈ GLBBetaFour G) (hD1 : D1At G q) {H : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (h3 : 3 ≤ Open.pRank q H) : ∃ Q : Sylow q G, GLBWeakCore q (Q : Subgroup G) ≤ H := by
  have hqp : q.Prime := hq.1
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained q hqp H
  have hE3 : ∀ K : Subgroup G, E ≤ K → 3 ≤ Open.pRank q K := fun K hEK =>
    (h3.trans (le_csSup (pRank_bddAbove q hqp E) ⟨E, le_rfl, hEel, hEcard⟩)).trans
      (pRank_mono q hqp hEK)
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hEcard).exists_le_sylow
  obtain ⟨L, hL, hWL⟩ := (hpre q hq).2 Q
  obtain ⟨Mq, hLMq, hMq⟩ := exists_maximal_twoLocal hL
  have hWMq : GLBWeakCore q (Q : Subgroup G) ≤ Mq := hWL.trans hLMq
  have hEMq : E ≤ Mq :=
    hEQ.trans ((subgroup_le_weakCore_of_rank q hqp (Q : Subgroup G) (hE3 _ hEQ)).trans hWMq)
  have hHMq : H ≤ Mq := hD1 Q Mq hMq hWMq H hH.1 (hE3 _ (le_inf hE hEMq))
  exact ⟨Q, (hH.2 Mq hMq.1 hHMq) ▸ hWMq⟩

omit [Finite G] in
theorem map_conj_map_conj_inv (Y : Subgroup G) (g : G) :
    (Y.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = Y := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  rw [e, Subgroup.map_id]

theorem exists_eq_map_conj_of_three_le_pRank (hpre : GLBPreuniqueness G) {q : ℕ}
    (hq : q ∈ GLBBetaFour G) (hD1 : D1At G q) {H M : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hM : GLBIsMaxTwoLocal M) (hH3 : 3 ≤ Open.pRank q H) (hM3 : 3 ≤ Open.pRank q M) :
    ∃ g : G, H = M.map (MulAut.conj g).toMonoidHom := by
  have hqp : q.Prime := hq.1
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨QH, hQH⟩ := exists_weakCore_le_of_three_le_pRank hpre hq hD1 hH hH3
  obtain ⟨QM, hQM⟩ := exists_weakCore_le_of_three_le_pRank hpre hq hD1 hM hM3
  obtain ⟨g, -, hg⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (QM : Subgroup G) ≤ ⊤) le_top QM.isPGroup' QH.isPGroup'
    (by
      change ¬ q ∣ (QM : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact QM.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity QH, Sylow.card_eq_multiplicity QM])
  have hQ3 : 3 ≤ Open.pRank q (QH : Subgroup G) :=
    hH3.trans (by
      rw [(SectionRank.pRank_sylow QH).1]
      exact SectionRank.pRank_mono hqp.one_lt le_top)
  have hcoreg : GLBWeakCore q (QH : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, glbWeakCore_map_conj hqp]
    exact Subgroup.map_mono hQM
  have hQHH : (QH : Subgroup G) ≤ H :=
    (subgroup_le_weakCore_of_rank q hqp _ hQ3).trans hQH
  have hQHM : (QH : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom :=
    (subgroup_le_weakCore_of_rank q hqp _ hQ3).trans hcoreg
  have h1 : M.map (MulAut.conj g).toMonoidHom ≤ H :=
    hD1 QH H hH hQH _ (isTwoLocal_map_conj hM.1 g)
      (hQ3.trans (pRank_mono q hqp (le_inf hQHM hQHH)))
  have h2 : M ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g * x * g⁻¹, h1 ⟨x, hx, rfl⟩, ?_⟩
    simp [mul_assoc]
  have h3 := hM.2 _ (isTwoLocal_map_conj hH.1 g⁻¹) h2
  refine ⟨g, ?_⟩
  rw [← h3, map_conj_map_conj_inv]

section Escape

variable {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.pRank_H (h : D2Escape p P M A H R) : Open.pRank p H = 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  rw [SectionRank.pRank_eq_pRank_top_subgroup H, ← (SectionRank.pRank_sylow T).1,
    ← pRank_map_of_injective p h.prime H.subtype H.subtype_injective, hT, h.pRank_eq]

theorem D2Escape.four_le_pRank_M (h : D2Escape p P M A H R) (hp : p ∈ GLBBetaFour G) :
    4 ≤ Open.pRank p M := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨L, -, hL⟩ := twoLocalRank_attained (G := G) p h.prime (by
    have := hp.2.2.2
    omega)
  have hG : 4 ≤ Open.pRank p (⊤ : Subgroup G) :=
    hp.2.2.2.trans (hL ▸ SectionRank.pRank_mono h.prime.one_lt le_top)
  rw [← (SectionRank.pRank_sylow P).1] at hG
  exact hG.trans (SectionRank.pRank_mono h.prime.one_lt h.sylow_le)

theorem D2Escape.false_of_three_le_pRank_both (h : D2Escape p P M A H R)
    (hpre : GLBPreuniqueness G) (hp : p ∈ GLBBetaFour G) {q : ℕ} (hq : q ∈ GLBBetaFour G)
    (hD1 : D1At G q) (hH3 : 3 ≤ Open.pRank q H) (hM3 : 3 ≤ Open.pRank q M) : False := by
  obtain ⟨g, hg⟩ :=
    exists_eq_map_conj_of_three_le_pRank hpre hq hD1 h.maxTwoLocal_H h.maxTwoLocal_M hH3 hM3
  have h4 := h.four_le_pRank_M hp
  have h2 := h.pRank_H
  rw [hg, pRank_map_of_injective p h.prime _ (MulAut.conj g).injective] at h2
  omega

end Escape

end CFSG.AGLEmbeddingD2
