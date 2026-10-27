module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDSp
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamULarge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def OddOrderAt (q p : ℕ) : Prop :=
  ∃ e : ℕ, 0 < e ∧ Odd e ∧ ∀ j : ℕ, p ∣ q ^ j - 1 ↔ e ∣ j

theorem statedClassicalModel_of_lieModel_of_ne_zero {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : CFSG.Models.LieModel G t n p f) :
    StatedClassicalModel G t n p f :=
  h.2.resolve_right fun h0 => hn h0.1

theorem crossAtOn_sp_of_model {d : TauCeti.ValidLieTypeIndex} {r : ℕ} (hr : 1 ≤ r)
    {q : TauCeti.PrimePower} (hchar : d.1.characteristic = q.p)
    (hmodel : ∀ (L : Type) [Group L], Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      StatedClassicalModel L .PSp r q.p q.exponent) :
    CrossAtOn d (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have core : ∀ (L : Type) [Group L] [Finite L] (p : ℕ), p.Prime → 5 ≤ p →
      OddOrderAt (q.p ^ q.exponent) p → d.1.characteristic ≠ p →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
        ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) ∧
      (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) → ∀ y : L, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))) := by
    intro L _ _ p hp hp5 hS hdp hiso
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmodel L hiso
    have hdp' : q.p ≠ p := by rwa [hchar] at hdp
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro h
      exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
    obtain ⟨e, he, heo, hpe⟩ := hS
    rw [← hK] at hpe
    exact cross_transport e' (crossAt_statedProj_sp_odd hp5 hr hpK he heo hpe)
  refine ⟨fun p hp hp5 hS hdp L _ _ hs hiso hn h2 P => ?_,
    fun p hp hp5 hS hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  · exact (core L p hp hp5 hS hdp hiso).1 h2 P
  · exact (core L p hp hp5 hS hdp hiso).2 h3 y (hy ▸ pow_orderOf_eq_one y)

theorem crossAtOn_C_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    CrossAtOn ⟨.C r q, hv⟩ (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  exact crossAtOn_sp_of_model hr1 (TauCeti.LieTypeIndex.characteristic_C r q)
    (fun L _ ⟨e⟩ => statedClassicalModel_of_lieModel_of_ne_zero (by omega)
      (CFSG.Models.lieModel_C r q hv e))

theorem crossAtOn_B_sp_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hb : r = 2 ∨ q.p = 2) :
    CrossAtOn ⟨.B r q, hv⟩ (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_sp_of_model hr1 (TauCeti.LieTypeIndex.characteristic_B r q)
    (fun L _ ⟨e⟩ => statedClassicalModel_of_lieModel_of_ne_zero (by omega) ?_)
  refine (CFSG.Models.lieModel_B r q hv e).resolve_right fun h => ?_
  obtain ⟨-, -, h3, h2⟩ := h.1
  rcases hb with hb | hb
  · omega
  · exact h2 hb

end CFSG.LocalAnalysis.RankFourTheoremC
