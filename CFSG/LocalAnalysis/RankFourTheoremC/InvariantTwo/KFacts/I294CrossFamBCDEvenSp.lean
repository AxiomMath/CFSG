module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenIso
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section Model

@[expose] noncomputable def statedSpEquiv (r : ℕ) (K : Type) [Field K] :
    StatedSp r K ≃* TauCeti.BilinForm.isometryGroup (pairedSympForm K r) :=
  ((TauCeti.BilinForm.isometryGroup (pairedSympForm K r)).equivMapOfInjective _
    (MulEquiv.injective _)).trans
    (MulEquiv.subgroupCongr (map_isometryGroup_eq_statedSp (r := r) (K := K))) |>.symm

end Model

section Core

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem crossAt_statedProj_sp_even (hp5 : 5 ≤ p) {r : ℕ} (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hee : Even e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hlarge : p * e ≤ 2 * r) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp r K))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedSp r K)),
        IsMulCommutative (R : Subgroup (StatedProj (StatedSp r K)))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp r K))) →
      ∀ y : StatedProj (StatedSp r K), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSp r K))))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have h5e : 5 ≤ p * e := by nlinarith
  have hr : 1 ≤ r := by omega
  have hp3e : 3 * e ≤ 2 * r := by nlinarith
  let eqv := statedSpEquiv r K
  have hrank : p ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedSp r K)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eqv]
    exact BCDEven.le_pRank_isometryGroup he hee ((hpe e).2 dvd_rfl) p (pairedSympForm K r)
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (by rw [finrank_standard]; exact hlarge)
  have hbig : ∀ y₀ : StatedSp r K, y₀ ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set (StatedSp r K))) := by
    intro y₀ hy₀
    have h := BCDEven.three_le_pRank_centralizer_isometry hp5 hpK he hee hpe (pairedSympForm K r)
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (by rw [finrank_standard]; exact hp3e)
      (eqv y₀) (by rw [← map_pow, hy₀, map_one])
    exact h.trans (pRank_centralizer_of_mulEquiv eqv y₀)
  have hidx : ¬ p ∣ (MonoidHom.id (StatedSp r K)).range.index := by
    have : (MonoidHom.id (StatedSp r K)).range = ⊤ :=
      MonoidHom.range_eq_top.2 Function.surjective_id
    rw [this, Subgroup.index_top]
    intro h
    have := Nat.le_of_dvd one_pos h
    omega
  exact crossAt_of_levi (d := p) hp5 ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K))
    (not_dvd_card_scalars_sp (by omega) hr) (MonoidHom.id (StatedSp r K)) Function.injective_id
    hidx (fun h => absurd h (lt_irrefl p)) hrank (fun _ => hbig)

end Core

section Family

theorem crossAtOn_sp_even_of_model {d : TauCeti.ValidLieTypeIndex} {r : ℕ}
    {q : TauCeti.PrimePower} (hchar : d.1.characteristic = q.p)
    (hmodel : ∀ (L : Type) [Group L], Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      StatedClassicalModel L .PSp r q.p q.exponent) :
    CrossAtOn d (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r) := by
  have core : ∀ (L : Type) [Group L] [Finite L] (p : ℕ), p.Prime → 5 ≤ p →
      (¬ OddOrderAt (q.p ^ q.exponent) p ∧ ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r) →
      d.1.characteristic ≠ p → Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
        ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) ∧
      (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) → ∀ y : L, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))) := by
    rintro L _ _ p hp hp5 ⟨hnodd, hnamb, -⟩ hdp hiso
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmodel L hiso
    have hdp' : q.p ≠ p := by rwa [hchar] at hdp
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro h
      exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
    obtain ⟨e, he, hpe⟩ := exists_order_data hpK
    have hpeQ : ∀ j : ℕ, p ∣ (q.p ^ q.exponent) ^ j - 1 ↔ e ∣ j := by rwa [hK] at hpe
    have hee : Even e := by
      by_contra hodd
      exact hnodd ⟨e, he, Nat.not_even_iff_odd.1 hodd, hpeQ⟩
    have hlarge : p * e ≤ 2 * r := by
      by_contra hlt
      exact hnamb ⟨e, he, hpeQ, (Nat.div_lt_iff_lt_mul he).2 (by omega)⟩
    exact cross_transport e' (crossAt_statedProj_sp_even hp5 hpK he hee hpe hlarge)
  refine ⟨fun p hp hp5 hS hdp L _ _ hs hiso hn h2 P => ?_,
    fun p hp hp5 hS hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  · exact (core L p hp hp5 hS hdp hiso).1 h2 P
  · exact (core L p hp hp5 hS hdp hiso).2 h3 y (hy ▸ pow_orderOf_eq_one y)

theorem crossFamCLarge : CrossFamCLarge := by
  intro r q hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  exact crossAtOn_sp_even_of_model (TauCeti.LieTypeIndex.characteristic_C r q)
    (fun L _ ⟨e⟩ => statedClassicalModel_of_lieModel_of_ne_zero (by omega)
      (CFSG.Models.lieModel_C r q hv e))

theorem crossFamBSpLarge : CrossFamBSpLarge := by
  intro r q hv hb
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_sp_even_of_model (TauCeti.LieTypeIndex.characteristic_B r q)
    (fun L _ ⟨e⟩ => statedClassicalModel_of_lieModel_of_ne_zero (by omega) ?_)
  refine (CFSG.Models.lieModel_B r q hv e).resolve_right fun h => ?_
  obtain ⟨-, -, h3, h2⟩ := h.1
  rcases hb with hb | hb
  · omega
  · exact h2 hb

end Family

end CFSG.LocalAnalysis.RankFourTheoremC
