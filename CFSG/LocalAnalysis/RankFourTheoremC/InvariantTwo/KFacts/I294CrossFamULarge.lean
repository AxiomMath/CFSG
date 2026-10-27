module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamLinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Restricted

@[expose] def CrossAbelianOn (d : TauCeti.ValidLieTypeIndex) (S : ℕ → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → S p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)

@[expose] def CrossRankOn (d : TauCeti.ValidLieTypeIndex) (S : ℕ → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → S p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) →
      ∀ y : L, orderOf y = p → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))

@[expose] def CrossAtOn (d : TauCeti.ValidLieTypeIndex) (S : ℕ → Prop) : Prop :=
  CrossAbelianOn d S ∧ CrossRankOn d S

@[expose] def CrossSylowAbelianOn (d : TauCeti.ValidLieTypeIndex) (S : ℕ → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → S p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ P : Sylow p L,
        IsMulCommutative (P : Subgroup L)

theorem crossAt_of_on_compl {d : TauCeti.ValidLieTypeIndex} {S : ℕ → Prop} (h : CrossAtOn d S)
    (hab : CrossSylowAbelianOn d (fun p => ¬ S p)) : CrossAt d := by
  refine ⟨fun p hp hp5 hdp L _ _ hs hiso hn h2 => ?_,
    fun p hp hp5 hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  · by_cases hSp : S p
    · exact h.1 p hp hp5 hSp hdp L hs hiso hn h2
    · exact hab p hp hp5 hSp hdp L hs hiso
  · by_cases hSp : S p
    · exact h.2 p hp hp5 hSp hdp L hs hiso hn h3 y hy
    · haveI : Fact p.Prime := ⟨hp⟩
      exact three_le_pRank_centralizer_of_sylow_abelian
        (fun P => hab p hp hp5 hSp hdp L hs hiso P) h3 (hy ▸ pow_orderOf_eq_one y)

end Restricted

section Unitary

@[expose] def UnitaryLarge (m : ℕ) (q : TauCeti.PrimePower) (p : ℕ) : Prop :=
  ∃ e : ℕ, 0 < e ∧ (∀ j : ℕ, p ∣ ((q.p ^ q.exponent) ^ 2) ^ j - 1 ↔ e ∣ j) ∧ p ≤ (m + 1) / e

@[expose] def CrossFamUnitaryLarge : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid),
    CrossAtOn ⟨.twistedA m q, hv⟩ (UnitaryLarge m q)

theorem crossSylowAbelianOn_unitary_small {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) :
    CrossSylowAbelianOn ⟨.twistedA m q, hv⟩ (fun p => ¬ UnitaryLarge m q p) := by
  intro p hp hp5 hlarge hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))).symm
  obtain ⟨e₀, he, hpe⟩ := exists_order_data (K := K) (p := p) hpK
  have hne : (m + 1) / e₀ < p := by
    by_contra hge
    exact hlarge ⟨e₀, he, fun j => by rw [← hK]; exact hpe j, not_lt.1 hge⟩
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => isMulCommutative_sylow_statedProj
      (fun P hP => isMulCommutative_of_isPGroup_GL_matrix
        (hp.odd_of_ne_two (by omega)) hpK he hpe hne hP)
      (StatedSU (m + 1) (q.p ^ q.exponent) K) R) P

theorem crossAt_unitary_of_large {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA m q).Valid}
    (h : CrossAtOn ⟨.twistedA m q, hv⟩ (UnitaryLarge m q)) : CrossAt ⟨.twistedA m q, hv⟩ :=
  crossAt_of_on_compl h (crossSylowAbelianOn_unitary_small hv)

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC
