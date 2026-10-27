module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcE
import CFSG.ClassicalInvolution.Orders.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem crossExcCl_card_orthogonalGroup_quadMinus {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  by_cases h2 : ℓ = 2
  · subst h2
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨hℓ⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    exact (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus m hirr).2
  · exact CFSG.ClassicalInvolution.card_orthogonalGroup_quadMinus_of_two_ne_zero
      (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hℓ h2 hK) hirr m

theorem crossAtPrime_B_odd_of_lt {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.p ≠ 2) (hr : 3 ≤ r) {p : ℕ} (hrp : r < p) :
    CrossAtPrime ⟨.B r q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq hr e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow q.prime_p hq hK
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedOmega_odd hp (by omega) hpK h2 hrp R) P

theorem crossAtPrime_D_of_lt {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) {p : ℕ} (hrp : r < p) :
    CrossAtPrime ⟨.D r q, hv⟩ p := by
  have hr : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedOmega_plus hp (by omega) hpK hrp R) P

theorem crossAtPrime_twistedD_of_lt {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) {p : ℕ} (hrp : r < p) :
    CrossAtPrime ⟨.twistedD r q, hv⟩ p := by
  have hr : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedOmega_minus hp (by omega) hpK
      (crossExcCl_card_orthogonalGroup_quadMinus q.prime_p hK hirr m) hrp R) P

end CFSG.LocalAnalysis.RankFourTheoremC
