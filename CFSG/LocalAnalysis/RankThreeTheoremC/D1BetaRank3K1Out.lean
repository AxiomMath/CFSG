module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem isPGroup_of_openIsElemAbelian {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem pRank_top_eq_zero_of_not_dvd {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card G) : Open.pRank p (⊤ : Subgroup G) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine Nat.le_zero.mp (SectionRank.pRank_le (k := 0) hp.one_lt fun E _ hE => ?_)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_openIsElemAbelian hE)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [hk]
  · exact absurd (dvd_trans (dvd_pow_self p hk0.ne') (hk ▸ Subgroup.card_subgroup_dvd_card E)) h

theorem pRank_mulAut_le_of_not_dvd_card_outer {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hZ : Subgroup.center K = ⊥) (T : Sylow p K)
    (hOut : ¬ p ∣ Nat.card (Outer K)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ Open.pRank p (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := pRank_attained p hp (⊤ : Subgroup (MulAut K))
  have h := elementary_rank_le_kernel_rank_add_image_rank p hp
    (QuotientGroup.mk' (inner K)) hE _ hcard
  rw [QuotientGroup.ker_mk'] at h
  have h1 : Open.pRank p (inner K) ≤ Open.pRank p (T : Subgroup K) := by
    have e1 : inner K = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) :=
      MonoidHom.range_eq_map _
    rw [e1, pRank_map_of_injective p hp _ (mulAut_conj_injective hZ),
      (CFSG.SectionRank.pRank_sylow T).1]
  have h2 : Open.pRank p (E.map (QuotientGroup.mk' (inner K))) = 0 :=
    Nat.le_zero.mp ((pRank_mono p hp le_top).trans (pRank_top_eq_zero_of_not_dvd hp hOut).le)
  omega

theorem not_dvd_card_outer_of_alternating {K : Type} [Group K] {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer K) := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact not_dvd_card_outer_alternatingGroup n hn p hp hp2

theorem pRank_mulAut_le_two_of_psl2 {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (e : K ≃* PSL(2, GaloisField p 2)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp1 := (Fact.out : p.Prime).one_lt
  rw [SectionRank.pRank_top_eq_of_mulEquiv hp1 (MulAut.congr e)]
  exact SectionRank.pRank_le hp1 fun E _ hE => kFactL2AutElemRank p 2 hp2 (by norm_num) E hE

theorem pRank_mulAut_le_two_of_unitary {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq1 : q.exponent = 1)
    (h : CFSG.RankThree.PartOne.Census3.IsoLie K (.twistedA 2 q)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hd : IsUnitaryIndex p ⟨.twistedA 2 q, hv⟩ := ⟨q, hqp, rfl⟩
  obtain ⟨q', -, hd', hfe, -⟩ := hd.exists_eq
  injection hd' with _ hqq
  subst hqq
  refine SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE => ?_
  have h := kFactUnitaryAutElemRank K p ⟨.twistedA 2 q, hv⟩ hd ⟨e⟩ E hE
  rwa [hfe, hq1] at h

end CFSG.LocalAnalysis.RankThreeTheoremC
