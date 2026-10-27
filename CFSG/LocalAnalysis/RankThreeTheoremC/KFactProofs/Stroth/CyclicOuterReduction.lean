module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterTools
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
import CFSG.Adapters.LinearCatalogStated
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def CharPCyclicSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), Nonempty (K ≃* Cat d) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
      ∀ T : Sylow p K, IsCyclic ↥(T : Subgroup K) → ¬ p ∣ Nat.card (Outer K)

@[expose] def SporadicOuterOdd : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)

theorem false_of_two_le_pRank {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    (hrk : RankLE1 p K) (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) : False := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h
  have := hrk E hE
  rw [hc] at this
  nlinarith [hp.two_le]

theorem stronglyEmbeddedCyclicOuter_of_inputs (hS : SeitzOuterRankOne) (hK3 : KFactOutCyclic)
    (hChar : CharPCyclicSylow) (hSpor : SporadicOuterOdd) (hTits : ∀ (K : Type) [Group K] [Finite
        K], IsoLie K .tits → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (Outer K)) :
    StronglyEmbeddedCyclicOuterKFact := by
  intro X _ _ K hKn hs hnab hcat hKC p hp hp2 P hPK hrank hΓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEP, hE, hEc, hEK, hT0⟩ := exists_plane hp hp2 hK3 K hs hnab hcat hKC P hPK hrank
  have hrk : RankLE1 p ↥K := rankLE1_of_isCyclic_inf hp P K hPK
  obtain ⟨T, hTcyc⟩ := exists_sylow_cyclic hp P K hPK
  obtain ⟨x, hxE, hxK⟩ := SetLike.not_le_iff_exists.1 hEK
  have hxp : x ^ p = 1 := hE.2 x hxE
  have hOut : ¬ p ∣ Nat.card (Outer ↥K) → False := fun hout =>
    hxK (mem_of_pow_eq_one_of_not_dvd_outer hp K hKC hout hxp)
  have hSeitz : ∀ (d : TauCeti.ValidLieTypeIndex) (e : ↥K ≃* Cat d),
      p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 → False := fun d e hpd hex =>
    hΓ (gamma_eq_top_of_generation hp P K hEP hE hT0
      (closure_fixed_eq_top_of_seitz hS hp hp2 K hKC d e hpd hex hE hEc hEK hrk))
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    refine hab (e.injective ?_)
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) (e a) (e b)
  | alternating n hn =>
    exfalso
    refine hOut ?_
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2
  | sporadic s =>
    exfalso
    refine hOut ?_
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hSpor s p hp hp2
  | lie d =>
    by_cases hchar : p = d.1.characteristic
    · exact (hOut (hChar ↥K d ⟨e⟩ p hp hp2 hchar T hTcyc)).elim
    · by_cases hex : IsD2SeitzException p d.1
      · rcases hex with ⟨hp3, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ |
          ⟨q, hq2, hq1, hd | hd⟩ | hd⟩ | ⟨hp5, hd | hd⟩
        ·
          refine Or.inl ⟨hp3, ?_⟩
          obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
            ⟨d, rfl⟩
          simp only at hd
          subst hd
          obtain ⟨qp, qe, hqp, hqe⟩ := q
          simp only at hq2 hq3
          subst hq2 hq3
          exact ⟨hv, ⟨e⟩⟩
        ·
          exfalso
          subst hp3
          obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
            ⟨d, rfl⟩
          simp only at hd
          subst hd
          have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
          obtain ⟨A, hA, hAc⟩ := exists_nine_of_psl hm (by norm_num)
            (by rw [hq2, hq2']; norm_num)
          have := hrk A hA
          rw [hAc] at this
          norm_num at this
        ·
          exfalso
          subst hp3
          exact false_of_two_le_pRank hp hrk (le_trans (by norm_num)
            (kFactSeitzRankThreeExceptions ↥K d ⟨q, hq2, hq1, Or.inl hd⟩ ⟨e⟩))
        ·
          exfalso
          subst hp3
          exact false_of_two_le_pRank hp hrk (le_trans (by norm_num)
            (kFactSeitzRankThreeExceptions ↥K d ⟨q, hq2, hq1, Or.inr (Or.inl hd)⟩ ⟨e⟩))
        ·
          exfalso
          subst hp3
          exact false_of_two_le_pRank hp hrk (le_trans (by norm_num)
            (kFactSeitzRankThreeExceptions ↥K d ⟨q, hq2, hq1, Or.inr (Or.inr hd)⟩ ⟨e⟩))
        ·
          exfalso
          obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
            ⟨d, rfl⟩
          simp only at hd
          subst hd
          exact hOut (hTits ↥K ⟨hv, ⟨e⟩⟩ p hp hp2)
        ·
          exfalso
          obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
            ⟨d, rfl⟩
          simp only at hd
          subst hd
          exact hOut (hTits ↥K ⟨hv, ⟨e⟩⟩ p hp hp2)
        ·
          refine Or.inr ⟨hp5, ?_⟩
          obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
            ⟨d, rfl⟩
          simp only at hd
          subst hd
          exact ⟨hv, ⟨e⟩⟩
      · exact (hSeitz d e hchar hex).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter
