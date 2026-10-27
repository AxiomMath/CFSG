module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CaseOne
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem eq_three_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
  have hp3 : p = 3 := by
    have hdvd : p ∣ 9 := h ▸ dvd_pow_self p hf0
    have : p ∣ 3 ^ 2 := by norm_num; exact hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow this)
  subst hp3
  have h' : 3 ^ f = 3 ^ 2 := by rw [h]; norm_num
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) h'⟩

theorem nonempty_psl2_galoisField_three :
    Nonempty (PSL2 (GaloisField 3 1) ≃* alternatingGroup (Fin 4)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num), pow_one]
  exact ⟨(psl2RingEquiv (ZMod.ringEquivOfPrime (GaloisField 3 1) Nat.prime_three
    hcard).symm).trans psl2_three_equiv_alternatingGroup⟩

theorem nonempty_pgl2_galoisField_three :
    Nonempty (PGL2 (GaloisField 3 1) ≃* Equiv.Perm (Fin 4)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num), pow_one]
  exact ⟨(pgl2RingEquiv (ZMod.ringEquivOfPrime (GaloisField 3 1) Nat.prime_three
    hcard).symm).trans pgl2_three_equiv_perm⟩

theorem dickson_root_pair {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hf2 : 2 ≤ f)
    (H : Subgroup (PSL2 K)) {r₁ r₂ y : PSL2 K} (hr₁H : r₁ ∈ H) (hr₂H : r₂ ∈ H) (hyH : y ∈ H)
    (hr₁ : r₁ ^ p = 1) (hr₁1 : r₁ ≠ 1) (hr₂ : r₂ ^ p = 1) (hr : r₁ * r₂ ≠ r₂ * r₁)
    (hy4 : 4 ≤ orderOf y) (hqy : Nat.card K ≤ 2 * orderOf y + 1) :
    H = ⊤ ∨ (Nat.card K = 9 ∧ ((orderOf y = 4 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      (orderOf y = 5 ∧ Nonempty (H ≃* alternatingGroup (Fin 5))))) := by
  classical
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  have hf0 : f ≠ 0 := by omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hKcard] at hqodd
    exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' hf0).mpr even_two)
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hq9 : 9 ≤ Nat.card K := by
    rw [hKcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf2
  have hpq : p ∣ Nat.card K := by rw [hKcard]; exact dvd_pow_self p hf0
  have hsmall : Nat.card K ≤ 11 → Nat.card K = 9 ∧ p = 3 ∧ f = 2 := by
    intro h11
    have hp3' : p = 3 := by
      by_contra hne
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp.out (by norm_num)
      have h5 : 5 ≤ p := by omega
      have : 25 ≤ Nat.card K := by
        rw [hKcard]
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left h5 2
          _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf2
      omega
    subst hp3'
    have hf2' : f = 2 := by
      by_contra hne
      have : 27 ≤ Nat.card K := by
        rw [hKcard]
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hf2'
    exact ⟨by rw [hKcard]; norm_num, rfl, rfl⟩
  set x₁ : H := ⟨r₁, hr₁H⟩ with hx₁def
  set x₂ : H := ⟨r₂, hr₂H⟩ with hx₂def
  set z : H := ⟨y, hyH⟩ with hzdef
  have hx₁₂ : x₁ * x₂ ≠ x₂ * x₁ := fun h => hr (congrArg Subtype.val h)
  have hzord : orderOf z = orderOf y := Subgroup.orderOf_mk y hyH
  have hr₁ord : orderOf r₁ = p := orderOf_eq_prime hr₁ hr₁1
  have hpH : p ∣ Nat.card H := by
    have h := orderOf_dvd_natCard x₁
    rwa [Subgroup.orderOf_mk, hr₁ord] at h
  have hbound : ∀ k : ℕ, (p ^ k) ^ 2 ≤ Nat.card K → orderOf y ≤ p ^ k + 1 →
      Nat.card K = 9 ∧ p = 3 ∧ f = 2 ∧ k = 1 := by
    intro k hk hle
    by_cases h11 : 11 ≤ Nat.card K
    · exact (subfield_order_absurd h11 hk hqy hle).elim
    · obtain ⟨h9, rfl, rfl⟩ := hsmall (by omega)
      refine ⟨h9, rfl, rfl, ?_⟩
      rw [h9] at hk
      rcases k with _ | _ | k
      · simp at hle
        omega
      · rfl
      · exfalso
        have : 3 ^ (k + 2) ≥ 9 := by
          calc 3 ^ (k + 2) ≥ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 9 := by norm_num
        nlinarith
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hKcard H with
    hEA | ⟨z', -, -, hcyc⟩ | ⟨z', hz', hz'card, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m', r, -, hr2, N, Cc, hNn, hNea, -, hCc, hCcard, -, hsup⟩ | ⟨k, hk0, hkf, ⟨eL⟩⟩ |
      ⟨k, hk0, hkf, ⟨eG⟩⟩
  · exact absurd (hEA.toIsMulCommutative.is_comm.comm x₁ x₂) hx₁₂
  · exact absurd (hcyc.commGroup.mul_comm x₁ x₂) hx₁₂
  ·
    exfalso
    rw [hz'card] at hpH
    have hpz : p ∣ z' :=
      (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2) hpH)
    have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
      apply Nat.gcd_eq_right
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k, by omega⟩
    rw [hgcd] at hz'
    obtain ⟨k, hk⟩ := hqodd
    rcases hz' with h | h
    · have h1 : p ∣ Nat.card K - 1 := (hpz.trans h).trans (Nat.div_dvd_of_dvd ⟨k, by omega⟩)
      have h2 : p ∣ 1 := by
        have := Nat.dvd_sub hpq h1
        rwa [show Nat.card K - (Nat.card K - 1) = 1 by omega] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
    · have h1 : p ∣ Nat.card K + 1 := (hpz.trans h).trans (Nat.div_dvd_of_dvd ⟨k + 1, by omega⟩)
      have h2 : p ∣ 1 := (Nat.dvd_add_right hpq).mp h1
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_four eA4 z with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  · rcases orderOf_dvd_of_equiv_perm_four eS4 z with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have h4 : orderOf y = 4 := by
        have := Nat.le_of_dvd (by norm_num) h
        omega
      obtain ⟨h9, -, -⟩ := hsmall (by omega)
      exact Or.inr ⟨h9, Or.inl ⟨h4, ⟨eS4⟩⟩⟩
  · rcases orderOf_dvd_of_equiv_alternating_five eA5 z with h | h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have h5 : orderOf y = 5 := by
        rw [← hzord]
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h' | h' <;> omega
      obtain ⟨h9, -, -⟩ := hsmall (by omega)
      exact Or.inr ⟨h9, Or.inr ⟨h5, ⟨eA5⟩⟩⟩
  ·
    exfalso
    have hcop : Nat.Coprime (Nat.card Cc) p := by
      rw [hCcard, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hpr
      have h1 : r ∣ Nat.card K - 1 := by
        rw [hKcard]
        exact hr2.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      have h2 : p ∣ Nat.card K - 1 := hpr.trans h1
      have h3 : p ∣ 1 := by
        have := Nat.dvd_sub hpq h2
        rwa [show Nat.card K - (Nat.card K - 1) = 1 by omega] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h3)
    have h₁N : x₁ ∈ N := mem_of_pow_eq_one_of_sup N Cc hsup hcop (Subtype.ext (by simpa using hr₁))
    have h₂N : x₂ ∈ N := mem_of_pow_eq_one_of_sup N Cc hsup hcop (Subtype.ext (by simpa using hr₂))
    have hcomm := hNea.toIsMulCommutative.is_comm.comm ⟨x₁, h₁N⟩ ⟨x₂, h₂N⟩
    exact hx₁₂ (congrArg Subtype.val hcomm)
  ·
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    by_cases hkf' : k = f
    · subst hkf'
      left
      apply Subgroup.eq_top_of_card_eq
      have hGFodd : IsOddPrimePower (Nat.card (GaloisField p k)) := hGF ▸ hKcard ▸ hK
      rw [Nat.card_congr eL.toEquiv, psl2_card_formula (GaloisField p k) hGFodd,
        psl2_card_formula K hK, hGF, hKcard]
    · exfalso
      have hle : orderOf y ≤ p ^ k + 1 := by
        rw [← hzord, ← MulEquiv.orderOf_eq eL z, ← hGF]
        exact psl2_orderOf_le _ _
      obtain ⟨-, rfl, rfl, rfl⟩ :=
        hbound k (hKcard ▸ pow_two_mul_le_of_dvd hp.out.one_lt.le hf0 hkf hkf') hle
      obtain ⟨eA⟩ := nonempty_psl2_galoisField_three
      rcases orderOf_dvd_of_equiv_alternating_four (eL.trans eA) z with h | h <;>
        · have := Nat.le_of_dvd (by norm_num) h
          omega
  ·
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hkf2 : k ∣ f := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hkf
    have hkf' : k ≠ f := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hkf
      omega
    have hle : orderOf y ≤ p ^ k + 1 := by
      rw [← hzord, ← MulEquiv.orderOf_eq eG z, ← hGF]
      exact pgl2_orderOf_le _ _
    obtain ⟨h9, rfl, rfl, rfl⟩ :=
      hbound k (hKcard ▸ pow_two_mul_le_of_dvd hp.out.one_lt.le hf0 hkf2 hkf') hle
    obtain ⟨eS⟩ := nonempty_pgl2_galoisField_three
    right
    refine ⟨h9, Or.inl ⟨by omega, ⟨eG.trans eS⟩⟩⟩

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
