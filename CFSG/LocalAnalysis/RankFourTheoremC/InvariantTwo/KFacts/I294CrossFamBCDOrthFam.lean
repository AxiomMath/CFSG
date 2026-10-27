module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthBT

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial

section Model

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem crossAt_statedProj_B_odd (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) (hpK : ¬ p ∣ Nat.card K)
    {e : ℕ} (he : 0 < e) (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hab : CFSG.IsElementaryAbelian 2
      (Abelianization (TauCeti.QuadraticMap.orthogonalGroup (quadOdd r K))))
    (hord : Nat.card (StatedProj (StatedOmega (StatedQuadOdd r K))) = ordBC r (Nat.card K)) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedOmega (StatedQuadOdd r K))),
        IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K))))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) →
      ∀ y : StatedProj (StatedOmega (StatedQuadOdd r K)), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p
          (centralizer ({y} : Set (StatedProj (StatedOmega (StatedQuadOdd r K)))))) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨w₀, hw₀⟩ := quadOdd_exists_one (s := r) (K := K)
  refine crossAt_statedProj_omega_levi (s := r) (e := e) hp5 hpK he hpe (coe_quadOdd r K) hab
    (quadOdd_smul) hw₀ (leviExt r Unit K) (leviExt_injective r Unit K) (quadOdd_leviExt) ?_
  rw [hord, padicValNat_card_GL_eq_sum hpK]
  exact padicValNat_ordBC hp5 heo hpe (fun h => hpK h) hq1 hr

theorem crossAt_statedProj_twistedD_odd (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r)
    (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e) (heo : Odd e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (b c : K)
    (hab : CFSG.IsElementaryAbelian 2
      (Abelianization (TauCeti.QuadraticMap.orthogonalGroup (quadMinus r K b c))))
    (hord : Nat.card (StatedProj (StatedOmega (StatedQuadMinus r K b c))) =
      ordTwistedD r (Nat.card K)) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedOmega (StatedQuadMinus r K b c))),
        IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c))))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) →
      ∀ y : StatedProj (StatedOmega (StatedQuadMinus r K b c)), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p
          (centralizer ({y} : Set (StatedProj (StatedOmega (StatedQuadMinus r K b c)))))) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨w₀, hw₀⟩ := quadMinus_exists_one r b c
  refine crossAt_statedProj_omega_levi (s := r - 1) (e := e) hp5 hpK he hpe
    (coe_quadMinus r K b c) hab (quadMinus_smul r b c) hw₀ (leviExt (r - 1) (Fin 2) K)
    (leviExt_injective (r - 1) (Fin 2) K) (quadMinus_leviExt r b c) ?_
  rw [hord, padicValNat_card_GL_eq_sum hpK]
  exact padicValNat_ordTwistedD hp5 heo hpe (fun h => hpK h) hq1 hr

end Model

section Family

theorem crossAtOn_B_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) :
    CrossAtOn ⟨.B r q, hv⟩ (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨e⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hdp
  rcases CFSG.Models.lieModel_B r q hv e with h | h
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro h
      exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
    obtain ⟨e₀, he₀, heo, hpe⟩ := hS
    rw [← hK] at hpe
    exact cross_transport e' (crossAt_statedProj_sp_odd hp5 hr1 hpK he₀ heo hpe)
  · have hmod : StatedClassicalModel L .POmegaOdd r q.p q.exponent :=
      statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    have hW := orthogonal_model_isometry_abelianization_order_bound
      L .POmegaOdd (Or.inl rfl) r q.p q.exponent hmod
    have hcardL := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hmod
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
    have hab := (hW K hK (quadOdd r K) (coe_quadOdd r K) e').1
    have hcard : Nat.card (StatedProj (StatedOmega (StatedQuadOdd r K))) =
        ordBC r (Nat.card K) := by
      rw [← Nat.card_congr e'.toEquiv, hcardL, hK]
      rfl
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro h
      exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
    obtain ⟨e₀, he₀, heo, hpe⟩ := hS
    rw [← hK] at hpe
    exact cross_transport e' (crossAt_statedProj_B_odd hp5 hr1 hpK he₀ heo hpe hab hcard)

theorem crossAtOn_twistedD_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨e⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hdp
  have hmod : StatedClassicalModel L .POmegaMinus r q.p q.exponent :=
    statedClassicalModel_of_lieModel_of_ne_zero (by omega) (CFSG.Models.lieModel_twistedD r q hv e)
  have hW := orthogonal_model_isometry_abelianization_order_bound
    L .POmegaMinus (Or.inr (Or.inr rfl)) r q.p q.exponent hmod
  have hcardL := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hmod
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ := hmod
  have hab := (hW K hK b c hirr (quadMinus r K b c) (coe_quadMinus r K b c) e').1
  have hcard : Nat.card (StatedProj (StatedOmega (StatedQuadMinus r K b c))) =
      ordTwistedD r (Nat.card K) := by
    rw [← Nat.card_congr e'.toEquiv, hcardL, hK]
    rfl
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨e₀, he₀, heo, hpe⟩ := hS
  rw [← hK] at hpe
  exact cross_transport e' (crossAt_statedProj_twistedD_odd hp5 hr1 hpK he₀ heo hpe b c hab hcard)

end Family

end CFSG.LocalAnalysis.RankFourTheoremC
