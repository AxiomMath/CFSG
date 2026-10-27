module

public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremC

open Subgroup CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem exists_isCoreWitness_of_two_le_pRank (hS : Standing G) (hUC : rankThreeUC G) {q : ℕ}
    (hq : q ∈ rankThreeSigmaA G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (h2 : 2 ≤ CFSG.Open.pRank q M) : ∃ Q : Sylow q G, IsCoreWitness q (Q : Subgroup G) M := by
  have hqp : q.Prime := sigmaA_prime q hq
  haveI : Fact q.Prime := ⟨hqp⟩
  obtain ⟨E, hEM, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (k := 2) h2
  have hEp : IsPGroup q E := elementary_isPGroup q E hE
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨P', M', hw'⟩ := rankThreeUC_iff.mp hUC q hq
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) P' Q
  have hPQ : (Q : Subgroup G) = (P' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← sylow_conjugate_eq_map, hg]
  have hcw : IsCoreWitness q (Q : Subgroup G) (M'.map (MulAut.conj g).toMonoidHom) := by
    have h := hw'.isCoreWitness.map hqp.one_lt (MulAut.conj g)
    rwa [← hPQ] at h
  have hQM₁ : (Q : Subgroup G) ≤ M'.map (MulAut.conj g).toMonoidHom :=
    le_normalizer.trans (hcw.normalizer_le hS hq)
  have hE2 : 2 ≤ CFSG.Open.pRank q (M ⊓ M'.map (MulAut.conj g).toMonoidHom) := by
    have hk : 2 ≤ CFSG.Open.pRank q E := CFSG.SectionRank.le_pRank hqp.one_lt (le_refl E) hE hEc
    exact hk.trans (pRank_mono q hqp.one_lt (le_inf hEM (hEQ.trans hQM₁)))
  have hM₁ : rankThreeIsMaxTwoLocal (M'.map (MulAut.conj g).toMonoidHom) :=
    rankThreeIsMaxTwoLocal_map hw'.maxLocal (MulAut.conj g)
  have hMM₁ : M ≤ M'.map (MulAut.conj g).toMonoidHom := hcw.u2 M hM.1 hE2
  have heq : M'.map (MulAut.conj g).toMonoidHom = M := hM.2 _ hM₁.1 hMM₁
  subst heq
  exact ⟨Q, hcw⟩

theorem le_of_mem_sigmaA (hS : Standing G) (hUC : rankThreeUC G) {q : ℕ}
    (hq : q ∈ rankThreeSigmaA G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQ2 : 2 ≤ CFSG.Open.pRank q Q) {H : Subgroup G}
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  have hqp : q.Prime := sigmaA_prime q hq
  have h2M : 2 ≤ CFSG.Open.pRank q M :=
    hQ2.trans (pRank_mono q hqp.one_lt hQM)
  obtain ⟨Q', hw⟩ := exists_isCoreWitness_of_two_le_pRank hS hUC hq hM h2M
  exact hw.u2 H hH
    (hQ2.trans (pRank_mono q hqp.one_lt (le_inf hQH hQM)))

end CFSG.LocalAnalysis.AGL81TheoremC
