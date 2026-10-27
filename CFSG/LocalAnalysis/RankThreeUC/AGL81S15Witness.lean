module

public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDNonsolvable
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isWitness_of_two_le_pRank (hS : Standing G) (hUC : rankThreeUC G) {q : ℕ}
    (hq : q ∈ rankThreeSigmaA G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hns : ¬ Group.IsSolvable ↥M) (h2 : 2 ≤ CFSG.Open.pRank q M) :
    ∃ Q : Sylow q G, IsWitness q Q M := by
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
    exact hk.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono q hqp.one_lt (le_inf hEM (hEQ.trans hQM₁)))
  have hM₁ : rankThreeIsMaxTwoLocal (M'.map (MulAut.conj g).toMonoidHom) :=
    rankThreeIsMaxTwoLocal_map hw'.maxLocal (MulAut.conj g)
  have hMM₁ : M ≤ M'.map (MulAut.conj g).toMonoidHom := hcw.u2 M hM.1 hE2
  have heq : M'.map (MulAut.conj g).toMonoidHom = M := hM.2 _ hM₁.1 hMM₁
  subst heq
  have hM'ns : ¬ Group.IsSolvable ↥M' := fun h =>
    hns (Group.isSolvable_of_surjective
      (f := (M'.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom)
      (M'.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective)
  have hΓ : rankThreeGamma 1 q (Q : Subgroup G) ≤ M'.map (MulAut.conj g).toMonoidHom := by
    rw [hPQ, ← gamma_map_automorphism 1 q hqp.one_lt (P' : Subgroup G) (MulAut.conj g)]
    exact Subgroup.map_mono (hw'.gamma_one_le_of_not_isSolvable hM'ns)
  exact ⟨Q, ⟨hM₁, hcw.u0, Or.inl hΓ, hcw.u2⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
