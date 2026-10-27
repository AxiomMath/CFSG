module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs
public import CFSG.Quasithin.Vol2.Ch11SecBL2UKp

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K3DvdL3Proof

theorem pow_mod_three_of_mod_one (q k : ℕ) (h : q % 3 = 1) : q ^ k % 3 = 1 := by
  rw [Nat.pow_mod, h]
  simp

theorem sq_mod_three_of_ne_zero {q : ℕ} (hq : q % 3 ≠ 0) : q ^ 2 % 3 = 1 := by
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h
  · exact pow_mod_three_of_mod_one q 2 h
  · rw [Nat.pow_mod, h]

theorem three_dvd_ordA_two {q : ℕ} (hq : q % 3 ≠ 0) : 3 ∣ CFSG.Open.ordA 2 q := by
  have hI : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  unfold CFSG.Open.ordA
  rw [hI, Finset.prod_pair (show (2 : ℕ) ≠ 3 by norm_num)]
  show 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)
  apply Nat.dvd_div_of_mul_dvd
  have h2 : 3 ∣ q ^ 2 - 1 := by
    have := sq_mod_three_of_ne_zero hq
    omega
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h
  · have h3 : 3 ∣ q - 1 := by omega
    have h3' : 3 ∣ q ^ 3 - 1 := by
      have := pow_mod_three_of_mod_one q 3 h
      omega
    rw [Nat.gcd_eq_left h3]
    exact Dvd.dvd.mul_left (Nat.mul_dvd_mul h2 h3') _
  · have hg : Nat.gcd 3 (q - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hg, one_mul]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _

end K3DvdL3Proof

theorem K3DvdL3_holds : K3DvdL3 := by
  intro S _ _ h
  rcases h with ⟨⟨t, hv⟩, ⟨Q, hQp, ht⟩, ⟨e⟩⟩ | ⟨⟨t, hv⟩, ⟨Q, hQc, ht⟩, ⟨e⟩⟩
  ·
    have ht' : t = TauCeti.LieTypeIndex.A 2 Q := ht
    subst ht'
    haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
    have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
    have hpsl := CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA
      (K := GaloisField Q.p Q.exponent) (n := 3) (by norm_num)
    rw [hK] at hpsl
    have hq3 : Q.card % 3 ≠ 0 := by
      rw [TauCeti.PrimePower.card_def, hQp]
      intro h3
      have h3' : 3 ∣ 2 ^ Q.exponent := Nat.dvd_of_mod_eq_zero h3
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
      omega
    have hcard : Nat.card S = CFSG.Open.ordA 2 Q.card := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).toEquiv).trans hpsl
    rw [hcard]
    exact K3DvdL3Proof.three_dvd_ordA_two hq3
  ·
    have ht' : t = TauCeti.LieTypeIndex.A 1 Q := ht
    subst ht'
    haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
    have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
    have hpsl := CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA
      (K := GaloisField Q.p Q.exponent) (n := 2) (by norm_num)
    rw [hK, hQc] at hpsl
    have hcard : Nat.card S = CFSG.Open.ordA (2 - 1) 7 := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv).toEquiv).trans hpsl
    have h168 : CFSG.Open.ordA (2 - 1) 7 = 168 := by decide
    rw [hcard, h168]
    norm_num

end CFSG.LocalAnalysis.RankThreeUC.S15
