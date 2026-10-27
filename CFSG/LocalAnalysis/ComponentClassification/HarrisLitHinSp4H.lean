module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Base
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatFactsSp4

theorem not_dvd_pow_sub_one {ℓ k n : ℕ} (hℓ : ℓ.Prime) (hℓk : ℓ ∣ k) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ¬ ℓ ∣ k ^ n - 1 := by
  intro hdvd
  have h1 : ℓ ∣ k ^ n := dvd_pow hℓk (by omega)
  have h2 : ℓ ∣ k ^ n - (k ^ n - 1) := Nat.dvd_sub h1 hdvd
  have h3 : k ^ n - (k ^ n - 1) = 1 := by
    have := Nat.one_le_pow n k (by omega)
    omega
  rw [h3] at h2
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

theorem false_of_field_order {ℓ e p m k : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (hk : k ^ 2 = ℓ ^ e) (hk3 : 3 ≤ k)
    (h : p ^ m * ((p ^ m) ^ 2 - 1) = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1))) : False := by
  set Q := p ^ m with hQ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hQ3 : 3 ≤ Q := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, pow_zero] at hk
      nlinarith
    · exact he
  have hℓk : ℓ ∣ k := hℓ.dvd_of_dvd_pow (show ℓ ∣ k ^ 2 by rw [hk]; exact dvd_pow_self ℓ (by omega))
  have hk4 : k ^ 4 = ℓ ^ (2 * e) := by
    rw [show k ^ 4 = (k ^ 2) ^ 2 by ring, hk, ← pow_mul, mul_comm]
  have hcopR : Nat.Coprime ℓ ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
    Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr (not_dvd_pow_sub_one hℓ hℓk (by omega) (by norm_num)))
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr (not_dvd_pow_sub_one hℓ hℓk (by omega) (by norm_num)))
  have hk4pos : 81 ≤ k ^ 4 := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk3 4
  have hk2pos : 9 ≤ k ^ 2 := by nlinarith
  by_cases hpl : p = ℓ
  · subst hpl
    have hpQ : p ∣ Q := dvd_pow_self p (by omega)
    have hcopQ : Nat.Coprime p (Q ^ 2 - 1) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_pow_sub_one hp hpQ (by omega) (by norm_num))
    have h1 : k ^ 4 ∣ Q := by
      have hc : Nat.Coprime (k ^ 4) (Q ^ 2 - 1) := by rw [hk4]; exact Nat.Coprime.pow_left _ hcopQ
      exact hc.dvd_of_dvd_mul_right ⟨_, h⟩
    have h2 : Q ∣ k ^ 4 := by
      have hc : Nat.Coprime Q ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
        rw [hQ]
        exact Nat.Coprime.pow_left _ hcopR
      exact hc.dvd_of_dvd_mul_right ⟨_, h.symm⟩
    have hQk : Q = k ^ 4 := Nat.dvd_antisymm h2 h1
    rw [hQk] at h
    have h3 : (k ^ 4) ^ 2 - 1 = (k ^ 2 - 1) * (k ^ 4 - 1) :=
      Nat.eq_of_mul_eq_mul_left (by omega) h
    have h4 : (k ^ 2 - 1) * (k ^ 4 - 1) ≤ k ^ 2 * k ^ 4 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h5 : k ^ 2 * k ^ 4 + 1 < (k ^ 4) ^ 2 := by nlinarith
    omega
  · have hcopℓp : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ hp).mpr (Ne.symm hpl)
    have hcopQ : Nat.Coprime (k ^ 4) Q := by
      rw [hk4, hQ]
      exact Nat.Coprime.pow _ _ hcopℓp
    have hdvd : k ^ 4 ∣ (Q ^ 2 - 1) := hcopQ.dvd_of_dvd_mul_left ⟨_, h⟩
    have hfac : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
      have : 1 ≤ Q ^ 2 := by nlinarith
      zify [this, (by omega : 1 ≤ Q)]
      ring
    rw [hfac] at hdvd
    have hbound : k ^ 4 ≤ Q + 1 := by
      by_cases hd1 : ℓ ∣ Q + 1
      · have hnd : ¬ ℓ ∣ Q - 1 := by
          intro hd2
          have h22 : ℓ ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub hd1 hd2
          rw [show (Q + 1) - (Q - 1) = 2 by omega] at h22
          exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h22)
        have hc : Nat.Coprime (k ^ 4) (Q - 1) := by
          rw [hk4]
          exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd)
        exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left hdvd)
      · have hc : Nat.Coprime (k ^ 4) (Q + 1) := by
          rw [hk4]
          exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd1)
        have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right hdvd)
        omega
    rw [hfac] at h
    have h6 : k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) ≤ (Q + 1) * ((k ^ 2 - 1) * Q) :=
      Nat.mul_le_mul hbound (Nat.mul_le_mul_left _ (by omega))
    have h7 : Q * ((Q - 1) * (Q + 1)) ≤ Q * ((Q + 1) * (k ^ 2 - 1)) := by
      calc Q * ((Q - 1) * (Q + 1)) = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := h
        _ ≤ (Q + 1) * ((k ^ 2 - 1) * Q) := h6
        _ = Q * ((Q + 1) * (k ^ 2 - 1)) := by ring
    have h8 : (Q - 1) * (Q + 1) ≤ (Q + 1) * (k ^ 2 - 1) := Nat.le_of_mul_le_mul_left h7 (by omega)
    have h9 : Q - 1 ≤ k ^ 2 - 1 := by
      rw [mul_comm] at h8
      exact Nat.le_of_mul_le_mul_left h8 (by omega)
    have h10 : k ^ 2 * 9 ≤ k ^ 4 := by nlinarith
    omega

theorem card_mul_two_of_lieModel_psl2 {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (hL : Blueprint.LieModel Z .PSL 2 p m) :
    Nat.card Z * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hodd := AutL2Facts.isOddPrimePower_of hpP hp2 hm1 hF'
  rw [Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
  have hev : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
    have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
      have : 16 ∣ (p ^ m) ^ 2 - 1 := by rwa [← pow_mul, mul_comm]
      exact (by norm_num : 2 ∣ 16).trans this
    exact h2.mul_left _
  exact Nat.div_mul_cancel hev

variable {K : Type} [Field K]

theorem conjAut_not_mem_range_conj [Finite K] (A : gsp 2 K)
    (hsq : ∀ l : K, l ^ 2 ≠ (multiplierUnit A : K)) :
    conjAut 2 K A ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [GSThmB.Cat7E6.conj_proj] at hx
  have h1 : conjAut 2 K ((⟨g, statedSp_le_gsp g.2⟩ : gsp 2 K)⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (GSThmB.Cat7E6.conjAut_eq_one_iff _).mp h1
  apply hsq c
  have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((c : K) • 1) := by
    have h2 : (A : GL (Fin 2 ⊕ Fin 2) K) = (g : GL (Fin 2 ⊕ Fin 2) K) *
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
      rw [← hc]
      simp
    rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hμ := multiplierUnit_spec A
  rw [hA] at hμ
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one] at hμ
  rw [symplectic_of_mem g, smul_smul] at hμ
  have hJ : (formJ 2 K) (Sum.inl 0) (Sum.inr 0) = 1 := by simp [formJ]
  have := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inr 0)
  simp only [Matrix.smul_apply, hJ, smul_eq_mul, mul_one] at this
  rw [← this, sq]

end CFSG.ComponentClassification.HarrisLit.Hin
