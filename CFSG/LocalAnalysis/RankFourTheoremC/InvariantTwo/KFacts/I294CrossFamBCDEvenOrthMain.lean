module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrthFam
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDAssembly2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial

section Data

theorem even_large_data {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.p ^ q.exponent) {p : ℕ} (hp : p.Prime) (hdp' : q.p ≠ p) {N : ℕ}
    (hnodd : ¬ OddOrderAt (q.p ^ q.exponent) p)
    (hnamb : ¬ AmbSmallAt N (q.p ^ q.exponent) p) :
    ¬ p ∣ Nat.card K ∧ ∃ e : ℕ, 0 < e ∧ Even e ∧
      (∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) ∧ p * e ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨e, he, hpe⟩ := exists_order_data hpK
  have hpeQ : ∀ j : ℕ, p ∣ (q.p ^ q.exponent) ^ j - 1 ↔ e ∣ j := by rwa [hK] at hpe
  have hee : Even e := by
    by_contra hodd
    exact hnodd ⟨e, he, Nat.not_even_iff_odd.1 hodd, hpeQ⟩
  have hlarge : p * e ≤ N := by
    by_contra hlt
    exact hnamb ⟨e, he, hpeQ, (Nat.div_lt_iff_lt_mul he).2 (by omega)⟩
  exact ⟨hpK, e, he, hee, hpe, hlarge⟩

end Data

section Families

theorem crossFamDEvenLarge : CrossFamDEvenLarge := by
  intro r q hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨eL⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hdp
  have hmod : StatedClassicalModel L .POmegaPlus r q.p q.exponent :=
    statedClassicalModel_of_lieModel_of_ne_zero (by omega) (CFSG.Models.lieModel_D r q hv eL)
  have hW := orthogonal_model_isometry_abelianization_order_bound
    L .POmegaPlus (Or.inr (Or.inl rfl)) r q.p q.exponent hmod
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
  have hab := (hW K hK (quadPlus r K) (coe_quadPlus r K) e').1
  obtain ⟨hnodd, hnamb, -⟩ := hS
  obtain ⟨hpK, e, he, hee, hpe, hlarge⟩ := even_large_data hK hp hdp' hnodd hnamb
  obtain ⟨w₀, hw₀⟩ := quadPlus_exists_one r K hr1
  exact cross_transport e' (crossAt_statedProj_omega_even hp5 hpK he hee hpe (coe_quadPlus r K)
    (nondegenerate_polarBilin_quadPlus r K) hab (quadPlus_smul r K) hw₀
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega))

theorem crossFamTwistedDEvenLarge : CrossFamTwistedDEvenLarge := by
  intro r q hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨eL⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hdp
  have hmod : StatedClassicalModel L .POmegaMinus r q.p q.exponent :=
    statedClassicalModel_of_lieModel_of_ne_zero (by omega)
      (CFSG.Models.lieModel_twistedD r q hv eL)
  have hW := orthogonal_model_isometry_abelianization_order_bound
    L .POmegaMinus (Or.inr (Or.inr rfl)) r q.p q.exponent hmod
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ := hmod
  have hab := (hW K hK b c hirr (quadMinus r K b c) (coe_quadMinus r K b c) e').1
  obtain ⟨hnodd, hnamb, -⟩ := hS
  obtain ⟨hpK, e, he, hee, hpe, hlarge⟩ := even_large_data hK hp hdp' hnodd hnamb
  obtain ⟨w₀, hw₀⟩ := quadMinus_exists_one r b c
  have hcard : Fintype.card (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) = 2 * r := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact cross_transport e' (crossAt_statedProj_omega_even hp5 hpK he hee hpe
    (coe_quadMinus r K b c) (nondegenerate_polarBilin_quadMinus_of_finite r K hirr) hab
    (quadMinus_smul r b c) hw₀ (by rw [hcard]; exact hlarge))

theorem crossFamBOrthEvenLarge : CrossFamBOrthEvenLarge := by
  intro r q hv hq2 hr3
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨eL⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hdp
  obtain ⟨hnodd, hnamb, -⟩ := hS
  rcases CFSG.Models.lieModel_B r q hv eL with h | h
  ·
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    obtain ⟨hpK, e, he, hee, hpe, hlarge⟩ := even_large_data hK hp hdp' hnodd hnamb
    have hev : Even (p * e) := hee.mul_left p
    obtain ⟨t, ht⟩ := hev
    exact cross_transport e' (crossAt_statedProj_sp_even hp5 hpK he hee hpe (by omega))
  ·
    have hmod : StatedClassicalModel L .POmegaOdd r q.p q.exponent :=
      statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    have hW := orthogonal_model_isometry_abelianization_order_bound
      L .POmegaOdd (Or.inl rfl) r q.p q.exponent hmod
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
    have hab := (hW K hK (quadOdd r K) (coe_quadOdd r K) e').1
    obtain ⟨hpK, e, he, hee, hpe, hlarge⟩ := even_large_data hK hp hdp' hnodd hnamb
    obtain ⟨w₀, hw₀⟩ := quadOdd_exists_one (s := r) (K := K)
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K q.p := charP_of_card_eq_prime_pow (p := q.p) (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
    have h2 : ringChar K ≠ 2 := by rw [ringChar.eq K q.p]; exact hq2
    have hcard : Fintype.card (Fin r ⊕ Fin r ⊕ Unit) = 2 * r + 1 := by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      omega
    exact cross_transport e' (crossAt_statedProj_omega_even hp5 hpK he hee hpe (coe_quadOdd r K)
      (nondegenerate_polarBilin_quadOdd r K (Ring.two_ne_zero h2)) hab quadOdd_smul hw₀
      (by rw [hcard]; exact hlarge))

end Families

end CFSG.LocalAnalysis.RankFourTheoremC
