module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR15
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR17

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

theorem hasL2Model_card {L : Type} [Group L] {P : ℕ → Prop} (hPr : ∀ q, P q → Odd q)
    (h : HasL2Model L P) : ∃ q : ℕ, P q ∧ 5 ≤ q ∧ Nat.card L = q * (q ^ 2 - 1) / 2 := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  obtain ⟨⟨hp', hf', hn2, h22, h23⟩, F, hFfield, hFfin, hF, ⟨e⟩⟩ :=
    CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hodd : Odd (p ^ f) := hPr _ hP
  have hq3 : p ^ f ≠ 3 := fun h3 => h23 (by rw [h3])
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hq5 : 5 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hoddF : Odd (Nat.card F) := hF ▸ hodd
  refine ⟨p ^ f, hP, hq5, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.ComponentClassification.CatFactsSp4.card_statedProj_statedSL_two_odd hoddF, hF]

theorem eight_dvd_of_isFM9 {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) (hfm : IsFM9 q) (hne : q ≠ 5) :
    8 ∣ q * (q ^ 2 - 1) / 2 := by
  obtain ⟨k, hk⟩ := hodd
  have hsq : q ^ 2 - 1 = 4 * (k * (k + 1)) := by
    apply Nat.sub_eq_of_eq_add
    rw [hk]
    ring
  have h4 : 4 ∣ k * (k + 1) := by
    rcases hfm with h9 | ⟨-, ⟨j, hj⟩ | ⟨n, hn⟩⟩
    · have hk4 : k = 4 := by omega
      subst hk4
      norm_num
    ·
      have hj2 : 2 ≤ j := by
        by_contra hlt
        push Not at hlt
        interval_cases j <;> simp at hj <;> omega
      have h16 : 2 ^ 2 ^ j = 16 * 2 ^ (2 ^ j - 4) := by
        have h4j : 4 ≤ 2 ^ j := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
        congr 1
        omega
      have : k = 8 * 2 ^ (2 ^ j - 4) := by omega
      exact Dvd.dvd.mul_right (by rw [this]; exact Dvd.dvd.mul_right (by norm_num) _) _
    ·
      have hn3 : 3 ≤ n := by
        by_contra hlt
        push Not at hlt
        interval_cases n <;> simp at hn <;> omega
      have h8 : 8 ∣ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ∣ 2 ^ n := pow_dvd_pow 2 hn3
      rw [← hn] at h8
      have h8' : 4 ∣ k + 1 := by omega
      exact Dvd.dvd.mul_left h8' _
  rw [hsq, show q * (4 * (k * (k + 1))) / 2 = q * (2 * (k * (k + 1))) by
    rw [show q * (4 * (k * (k + 1))) = 2 * (q * (2 * (k * (k + 1)))) by ring]
    omega]
  obtain ⟨m, hm⟩ := h4
  rw [hm]
  exact ⟨q * m, by ring⟩

section Dihedral

variable {G : Type} [Group G] [Finite G]

theorem exists_dihedral_P {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S)
    (hK : HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(T ⊓ K) ≃* DihedralGroup (2 ^ (n - 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdihK : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar K) :=
    hasDihedralSylowTwo_of_hasL2Model (fun q hq => hq.1) hK
  have hdihK' : CFSG.GorensteinWalter.HasDihedralSylowTwo ↥K := hasDihedralSylowTwo_of_kBar hdihK
  obtain ⟨Q, hQ⟩ := hstd.sylow_P
  obtain ⟨m, hm1, ⟨e⟩⟩ := hdihK' Q
  obtain ⟨q, hq, hq5, hcard⟩ := hasL2Model_card (fun q hq => hq.1) hK
  have h8 : 8 ∣ Nat.card (kBar K) := hcard ▸ eight_dvd_of_isFM9 hq.1 hq5 hq.2.1 hq.2.2
  have h8K : 8 ∣ Nat.card ↥K :=
    h8.trans (Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _))
  have hQcard : Nat.card ↥Q = 2 ^ (Nat.card ↥K).factorization 2 := Q.card_eq_multiplicity
  have hv : 3 ≤ (Nat.card ↥K).factorization 2 := by
    have hpos : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 (by simpa using h8K)
  have hcardQ : Nat.card ↥Q = 2 * 2 ^ m := by
    have h1 := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at h1
    exact h1
  have hm2 : 2 ≤ m := by
    have h1 : 2 ^ (m + 1) = 2 ^ (Nat.card ↥K).factorization 2 := by
      rw [pow_succ, mul_comm, ← hcardQ, hQcard]
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  refine ⟨m + 1, by omega, ⟨?_⟩⟩
  have eP : ↥(T ⊓ K) ≃* ↥Q :=
    (MulEquiv.subgroupCongr hQ.symm).trans
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥K) K.subtype K.subtype_injective).symm
  have hdm : m + 1 - 1 = m := by omega
  rw [hdm]
  exact eP.trans e

end Dihedral

end CFSG.GH74.GLS.Th2.Obs
