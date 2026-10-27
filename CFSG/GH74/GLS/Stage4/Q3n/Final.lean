module

public import CFSG.GH74.GLS.Stage4.Q3n.ProdCard
public import CFSG.CharacterTheory.KleinFourBlocks.CentralProduct
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open CFSG

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨j, rfl⟩ := hq
  have h1 : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
  have h2 : 2 ∣ j * (j + 1) := (Nat.even_mul_succ_self j).two_dvd
  obtain ⟨c, hc⟩ := h2
  rw [h1, hc]
  omega

theorem padic_two_sub_one_add_one {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q - 1) + 1 ≤ padicValNat 2 (q ^ 2 - 1) ∧
      padicValNat 2 (q + 1) + 1 ≤ padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : q % 2 = 1 := Nat.odd_iff.1 hq
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (j + 1) ^ 2 - 1 = j * (j + 2) := by
      have : (j + 1) ^ 2 = j * (j + 2) + 1 := by ring
      omega
    rw [this]
  have h1 : q - 1 ≠ 0 := by omega
  have h2 : q + 1 ≠ 0 := by omega
  have e1 : 1 ≤ padicValNat 2 (q - 1) := one_le_padicValNat_of_dvd h1 (by omega)
  have e2 : 1 ≤ padicValNat 2 (q + 1) := one_le_padicValNat_of_dvd h2 (by omega)
  rw [hfac, padicValNat.mul h1 h2]
  omega

theorem padic_two_le_of_dvd_cases {q d a m : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (hd : d = 1 ∨ d = q ∨ d = q - 1 ∨ d = q + 1) (ha : 0 < a) (hm : 0 < m) (hda : d = a * m) :
    padicValNat 2 m + 1 ≤ padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 := eight_dvd_sq_sub_one hq
  have hV3 : 3 ≤ padicValNat 2 (q ^ 2 - 1) := by
    have hne : q ^ 2 - 1 ≠ 0 := by
      have : 1 < q ^ 2 := by nlinarith
      omega
    exact (padicValNat_dvd_iff_le hne).1 (by simpa using h8)
  have hmd : padicValNat 2 m ≤ padicValNat 2 d := by
    have hd0 : d ≠ 0 := by rw [hda]; positivity
    rw [hda, padicValNat.mul ha.ne' hm.ne']
    omega
  obtain ⟨h1, h2⟩ := padic_two_sub_one_add_one hq hq3
  have hq0 : padicValNat 2 q = 0 := padicValNat.eq_zero_of_not_dvd (by
    have := Nat.odd_iff.1 hq; omega)
  rcases hd with h | h | h | h
  · rw [h, padicValNat_one_right] at hmd; omega
  · rw [h, hq0] at hmd; omega
  · rw [h] at hmd; omega
  · rw [h] at hmd; omega

theorem final_contradiction {n : ℕ} (hn : 1 ≤ n)
    {M : Type} [Group M] [Finite M] (K₁ K₂ : Subgroup M)
    (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n))
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n))
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hnorm : (K₁ ⊔ K₂).Normal) (hidx : (K₁ ⊔ K₂).index ≤ 2)
    (hinter : Nat.card ↥(K₁ ⊓ K₂) = 2)
    (ζ : M → ℂ) (hζ : ζ ∈ BlocksIrr M) (d : ℕ) (hd : ζ 1 = d)
    (h2 : 2 ^ ((Nat.card M).factorization 2 - 2) ∣ d) (h3 : 3 ∣ d) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqF : Nat.card (GaloisField 3 n) = 3 ^ n := GaloisField.card 3 n (by omega)
  have hqodd : Odd (3 ^ n) := Odd.pow (by decide)
  have hq3 : 3 ≤ 3 ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fintype (GaloisField 3 n) := Fintype.ofFinite _
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 n)) =
      3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hqF]
  have hK₁ : Nat.card ↥K₁ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by rw [Nat.card_congr e₁.toEquiv, hSL]
  have hK₂ : Nat.card ↥K₂ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by rw [Nat.card_congr e₂.toEquiv, hSL]
  have hprod := card_sup_mul_card_inf hcomm
  rw [hinter, hK₁, hK₂] at hprod
  have hM : Nat.card ↥(K₁ ⊔ K₂) * (K₁ ⊔ K₂).index = Nat.card M := Subgroup.card_mul_index _
  set idx := (K₁ ⊔ K₂).index with hidx_def
  set q := 3 ^ n with hq
  have hM2 : Nat.card M * 2 = idx * (q * (q ^ 2 - 1)) ^ 2 := by
    rw [← hM]
    calc Nat.card ↥(K₁ ⊔ K₂) * idx * 2 = idx * (Nat.card ↥(K₁ ⊔ K₂) * 2) := by ring
      _ = idx * (q * (q ^ 2 - 1) * (q * (q ^ 2 - 1))) := by rw [hprod]
      _ = idx * (q * (q ^ 2 - 1)) ^ 2 := by ring
  have hidx0 : idx ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hq1 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := by nlinarith
    omega
  have hq0 : q ≠ 0 := by omega
  have hqv : padicValNat 2 q = 0 := padicValNat.eq_zero_of_not_dvd (by
    have := Nat.odd_iff.1 hqodd; omega)
  have hval := congrArg (padicValNat 2) hM2
  rw [padicValNat.mul hM0 (by norm_num), padicValNat.mul hidx0 (pow_ne_zero 2 (mul_ne_zero hq0 hq1)),
    padicValNat.pow (q * (q ^ 2 - 1)) 2, padicValNat.mul hq0 hq1, hqv] at hval
  have hp2 : padicValNat 2 2 = 1 := by simp
  rw [hp2] at hval
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, e, he, hdeg⟩ :=
    CFSG.KleinFourBlocks.iv2_10_5_of_index_le_two M K₁ K₂ hcomm hnorm hidx ζ hζ
  have hθ₁ := CFSG.Semidihedral.OddFieldSL2Degree.comp_mulEquiv_mem_blocksIrr e₁.symm hζ₁
  have hθ₂ := CFSG.Semidihedral.OddFieldSL2Degree.comp_mulEquiv_mem_blocksIrr e₂.symm hζ₂
  obtain ⟨n₁, hn₁, hn₁pos, ⟨d₁, a₁, hd₁, ha₁, hda₁⟩, -, h6₁⟩ :=
    CFSG.Semidihedral.OddFieldSL2Degree.odd_field_SL2_irreducible_degree_is_not_divisible_by_two_times_characteristic
      Nat.prime_three (by decide) hn hqF _ hθ₁
  obtain ⟨n₂, hn₂, hn₂pos, ⟨d₂, a₂, hd₂, ha₂, hda₂⟩, -, h6₂⟩ :=
    CFSG.Semidihedral.OddFieldSL2Degree.odd_field_SL2_irreducible_degree_is_not_divisible_by_two_times_characteristic
      Nat.prime_three (by decide) hn hqF _ hθ₂
  rw [hqF] at hd₁ hd₂
  have hn₁' : ζ₁ 1 = n₁ := by simpa using hn₁
  have hn₂' : ζ₂ 1 = n₂ := by simpa using hn₂
  have hdnat : d = e * (n₁ * n₂) := by
    have : (d : ℂ) = e * (n₁ * n₂) := by rw [← hd, hdeg, hn₁', hn₂']
    exact_mod_cast this
  have hb₁ := padic_two_le_of_dvd_cases hqodd hq3 hd₁ ha₁ hn₁pos hda₁
  have hb₂ := padic_two_le_of_dvd_cases hqodd hq3 hd₂ ha₂ hn₂pos hda₂
  have hV3 : 3 ≤ padicValNat 2 (q ^ 2 - 1) := by
    have hne : q ^ 2 - 1 ≠ 0 := hq1
    exact (padicValNat_dvd_iff_le hne).1 (by simpa using eight_dvd_sq_sub_one hqodd)
  have hd0 : d ≠ 0 := by
    have := blocksIrr_identity_re_pos ⟨ζ, hζ⟩
    rintro rfl
    simp [hd] at this
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hdnat
    exact hd0 hdnat
  rw [Nat.factorization_def _ Nat.prime_two] at h2
  have hdv : padicValNat 2 (Nat.card M) - 2 ≤ padicValNat 2 d := (padicValNat_dvd_iff_le hd0).1 h2
  have hdv' : padicValNat 2 d = padicValNat 2 e + (padicValNat 2 n₁ + padicValNat 2 n₂) := by
    rw [hdnat, padicValNat.mul he0 (mul_ne_zero hn₁pos.ne' hn₂pos.ne'),
      padicValNat.mul hn₁pos.ne' hn₂pos.ne']
  have he' : e ∣ idx := he
  have hev : padicValNat 2 e ≤ padicValNat 2 idx := by
    obtain ⟨c, hc⟩ := he'
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
      exact hidx0 hc
    rw [hc, padicValNat.mul he0 hc0]
    omega
  have hx1 : 1 ≤ padicValNat 2 n₁ := by omega
  have hy1 : 1 ≤ padicValNat 2 n₂ := by omega
  have h2n₁ : 2 ∣ n₁ := dvd_of_one_le_padicValNat hx1
  have h2n₂ : 2 ∣ n₂ := dvd_of_one_le_padicValNat hy1
  have he2 : e ≤ 2 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hidx0) he').trans hidx
  have h3n : 3 ∣ n₁ ∨ 3 ∣ n₂ := by
    have h3' : 3 ∣ e * (n₁ * n₂) := hdnat ▸ h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3' with h | h
    · exfalso
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) h
      omega
    · exact (Nat.Prime.dvd_mul Nat.prime_three).1 h
  rcases h3n with h | h
  · exact h6₁ (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2n₁ h)
  · exact h6₂ (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2n₂ h)

end CFSG.GH74.GLS.Stage4.Q3n
