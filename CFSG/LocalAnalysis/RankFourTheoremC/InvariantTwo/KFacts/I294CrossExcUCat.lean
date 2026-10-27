module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUBase
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamULarge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CrossExcU

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Subgroup

namespace CrossExcU

section Numerics

theorem unitaryOrder_pos {ℓ f p : ℕ} (hp : p.Prime) (hpℓ : ¬ p ∣ ℓ) : 0 < unitaryOrder ℓ f p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (-((ℓ ^ f : ℕ) : ZMod p)) ≠ 0 := fun h0 => by
    have h1 := (ZMod.natCast_eq_zero_iff (ℓ ^ f) p).1 (neg_eq_zero.1 h0)
    exact hpℓ (hp.dvd_of_dvd_pow h1)
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by have := hp.two_le; omega,
    ZMod.pow_card_sub_one_eq_one hq0⟩)

theorem unitaryOrder_dvd_iff {ℓ f p : ℕ} (j : ℕ) :
    unitaryOrder ℓ f p ∣ j ↔ (-((ℓ ^ f : ℕ) : ZMod p)) ^ j = 1 :=
  orderOf_dvd_iff_pow_eq_one

end Numerics

end CrossExcU

section Catalog

theorem crossAbelianOn_unitary_of_props (hR1 : UnitaryRankProp) (hR2 : UnitaryAbelianProp)
    {m : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) :
    CrossAbelianOn ⟨.twistedA m q, hv⟩ (UnitaryLarge m q) := by
  intro p hp hp5 _ hdp L _ _ hs ⟨e⟩ hn h2 P
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hℓp : ¬ p ∣ q.p := fun hd =>
    hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 hd).symm
  have hg : ¬ (p ∣ m + 1 ∧ p ∣ q.p ^ q.exponent + 1) := fun ⟨h1, h1'⟩ =>
    hn (Or.inr ⟨m + 1, q.p ^ q.exponent, K, inferInstance, inferInstance, hK, h1, h1', ⟨e'⟩⟩)
  have hKf : UnitaryFieldData q.p q.exponent K :=
    ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2' : CFSG.Open.pRank p
      (⊤ : Subgroup (StatedProj (StatedSU (m + 1) (q.p ^ q.exponent) K))) = 2 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e').symm.trans h2
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcU_abelian_statedProj hKf (by omega) hp5 hg
      (unitaryOrder_pos hp hℓp) (hR1 q.p q.exponent K hKf (m + 1) p hp hp5 hℓp)
      (hR2 q.p q.exponent K hKf (m + 1) p hp hp5 hℓp) h2' R) P

theorem crossRankOn_unitary_of_props (hR1 : UnitaryRankProp) (hR2 : UnitaryAbelianProp) {m : ℕ}
    {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) :
    CrossRankOn ⟨.twistedA m q, hv⟩ (UnitaryLarge m q) := by
  intro p hp hp5 _ hdp L _ _ hs ⟨e⟩ hn h3 y hy
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hℓp : ¬ p ∣ q.p := fun hd =>
    hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 hd).symm
  have hg : ¬ (p ∣ m + 1 ∧ p ∣ q.p ^ q.exponent + 1) := fun ⟨h1, h1'⟩ =>
    hn (Or.inr ⟨m + 1, q.p ^ q.exponent, K, inferInstance, inferInstance, hK, h1, h1', ⟨e'⟩⟩)
  have hKf : UnitaryFieldData q.p q.exponent K :=
    ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  have hyp : (e' y) ^ p = 1 := by
    rw [← map_pow, (hy ▸ pow_orderOf_eq_one y : y ^ p = 1), map_one]
  have h3' : 3 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (StatedProj (StatedSU (m + 1) (q.p ^ q.exponent) K))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e').symm ▸ h3
  exact (crossExcU_rank_statedProj_full hKf (by omega) hp5 hg (unitaryOrder_pos hp hℓp)
    (hR1 q.p q.exponent K hKf (m + 1) p hp hp5 hℓp)
    (hR2 q.p q.exponent K hKf (m + 1) p hp hp5 hℓp) h3' (e' y) hyp).trans
    (pRank_centralizer_of_mulEquiv e' y)

theorem crossFamUnitaryLarge_of_props (hR1 : UnitaryRankProp) (hR2 : UnitaryAbelianProp) :
    CrossFamUnitaryLarge := fun _ _ _ hv =>
  ⟨crossAbelianOn_unitary_of_props hR1 hR2 hv, crossRankOn_unitary_of_props hR1 hR2 hv⟩

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
