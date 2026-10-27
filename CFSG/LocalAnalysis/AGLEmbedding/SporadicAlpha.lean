module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

theorem kOutTwoGroup_of_card_outer_le_two {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hOut : Nat.card (Outer (K ⧸ Subgroup.center K)) ≤ 2) :
    KOutTwoGroup K := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hdvd : Nat.card (Outer (K ⧸ Subgroup.center K)) ∣ 2 :=
    (Nat.dvd_prime Nat.prime_two).mpr (by
      have := Nat.card_pos (α := Outer (K ⧸ Subgroup.center K))
      omega)
  intro f
  refine ⟨1, ?_⟩
  have h1 : QuotientGroup.mk' (inner K) (f ^ 2) = 1 := by
    apply centerQuotient_outer_injective K
    rw [map_one, map_pow, map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hdvd)
  rw [pow_one]
  exact (QuotientGroup.eq_one_iff (N := inner K) _).mp h1

theorem pRank_top_mulAut_le_two_of_cover {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) {X : Type} [Group X] (e : K ⧸ Subgroup.center K ≃* X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hOut : Nat.card (Outer X) ≤ 2)
    (h : ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨a, b, hab⟩ :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian
    e.symm.isSimpleGroup ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hOutp : ¬ p ∣ Nat.card (Outer X) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    have := hp.two_le
    omega
  have h1 := SectionRank.pRank_top_le_of_injective hp.one_lt
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  rw [SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)] at h1
  refine h1.trans ((pRank_top_mulAut_le_of_not_dvd hp hZ hOutp).trans ?_)
  rcases h with h3 | ⟨h4, hpair⟩
  · exact RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hp h3
  · exact pRank_le_two_of_hasNoncommPair hp h4 hpair

section Transport

variable {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}

include e in
theorem ModuleDatum.of_mulEquiv : ModuleDatum X p → ModuleDatum Y p := by
  rintro ⟨D, hn, hA, hF, P, hP⟩
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hinj' : Function.Injective e.symm.toMonoidHom := e.symm.injective
  have hle : (P : Subgroup X) ≤ e.symm.toMonoidHom.range := fun x _ =>
    MonoidHom.mem_range.mpr ⟨e x, e.symm_apply_apply x⟩
  refine ⟨D.map e.toMonoidHom hinj, hn, hA, hF,
    P.comapOfInjective e.symm.toMonoidHom hinj' hle, ?_⟩
  rw [Sylow.coe_comapOfInjective, ← Subgroup.map_equiv_eq_comap_symm', ModuleSpec.map_span]
  exact (Subgroup.map_mono hP).trans (Subgroup.le_normalizer_map _)

include e in
theorem AbelianSylowDatum.of_mulEquiv : AbelianSylowDatum X p → AbelianSylowDatum Y p := by
  rintro ⟨D, hn, hF, hN, hi⟩
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨D.map e.toMonoidHom hinj, hn, hF, hN, ?_⟩
  rwa [ModuleSpec.map_span, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]

end Transport

theorem kFactAlphaConclusion_of_data (hmod : CoverModuleLemma) (hab : CoverAbelianSylowLemma)
    (hrl : CoverRankLiftLemma) (K : Type) [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    {X : Type} [Group X] (e : K ⧸ Subgroup.center K ≃* X) (h : SporadicAlphaData X) :
    KFactAlphaConclusion K := by
  intro p hp hp2 hZ hZp hZc T
  obtain ⟨hOut, hdata⟩ := h
  set π : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp [π]
  have hOut' : Nat.card (Outer (K ⧸ Subgroup.center K)) ≤ 2 :=
    (Nat.card_congr (equivalence e).toEquiv).trans_le hOut
  rcases hdata p hp hp2 with hsmall | hm | ha | hr
  · exact Or.inr (Or.inl (pRank_top_mulAut_le_two_of_cover hK e hp hp2 hOut hsmall))
  · exact Or.inr (Or.inr (Or.inr ⟨kOutTwoGroup_of_card_outer_le_two hK hOut',
      Or.inr (Or.inr (hmod K X π hπ hker p hp hp2 hZ hZp hZc hm T))⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨kOutTwoGroup_of_card_outer_le_two hK hOut',
      Or.inr (Or.inl (hab K X π hπ hker ⟨hK.1⟩ p hp hp2 hZ hZp hZc ha T))⟩))
  · have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
    have : Nontrivial X := e.injective.nontrivial
    exact Or.inr (Or.inr (Or.inl (hrl K X π hπ hker p hp hp2 hZ hZp hZc hr T)))

end CFSG.AGLEmbedding
