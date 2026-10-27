module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LGF3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LMain

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem antiW_inv : (antiW : GL (Fin 3) K)⁻¹ = antiW :=
  Units.ext rfl

theorem antiW_mul_self : (antiW : GL (Fin 3) K) * antiW = 1 := by
  calc (antiW : GL (Fin 3) K) * antiW = antiW * antiW⁻¹ := by rw [antiW_inv]
    _ = 1 := mul_inv_cancel _

theorem inverseTranspose_antiW :
    GeneralLinearGroup.inverseTranspose (antiW : GL (Fin 3) K) = antiW := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, antiW_inv]
  change ((Equiv.swap (0 : Fin 3) 2).permMatrix K)ᵀ = (Equiv.swap (0 : Fin 3) 2).permMatrix K
  rw [transpose_permMatrix, Equiv.swap_inv]

theorem map_antiW (σ : K ≃+* K) :
    GeneralLinearGroup.map (σ : K →+* K) (antiW : GL (Fin 3) K) = antiW := by
  apply Units.ext
  ext i j
  change σ ((Equiv.swap (0 : Fin 3) 2).permMatrix K i j) =
    (Equiv.swap (0 : Fin 3) 2).permMatrix K i j
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem sq_antiW_fieldAut_dualAut {σ : K ≃+* K} (hσσ : σ * σ = 1) :
    (conjAut 3 K antiW * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1 := by
  rw [sq_conjAut_fieldAut_dualAut, inverseTranspose_antiW, map_antiW, hσσ, map_one, mul_one,
    antiW_mul_self, map_one]

theorem hasWit_antiW [Finite K] (h2 : (2 : K) = 0) {σ : K ≃+* K} {a : K} (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) (hσa : σ a = a) :
    HasWit (conjAut 3 K antiW * fieldAut 3 K σ * dualAut 3 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set E : Matrix (Fin 3) (Fin 3) K := eij 0 2 with hE
  have hEE : E * E = 0 := by rw [hE, eij_mul_eij]; simp
  set τ := torus3 a ha0 with hτ
  have hEτ : E * (τ : Matrix (Fin 3) (Fin 3) K) = a⁻¹ • E := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hτ, coe_torus3, hE, eij, Matrix.mul_apply, Matrix.single_apply]
  have hτE : (τ : Matrix (Fin 3) (Fin 3) K) * E = a • E := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hτ, coe_torus3, hE, eij, Matrix.mul_apply, Matrix.single_apply]
  have hEτ' : E * ((τ⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a • E := by
    rw [hτ, torus3_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_torus3, hE, eij, Matrix.mul_apply, Matrix.single_apply]
  have hev := (FiniteField.even_card_iff_char_two (F := K)).mp (ringChar_eq_two h2)
  have hK2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hm : Odd (Fintype.card K - 1) := Nat.odd_iff.mpr (by omega)
  have hτm : τ ^ (Fintype.card K - 1) = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hτ, coe_torus3, diagonal_pow]
    fin_cases i <;> fin_cases j <;>
      simp [FiniteField.pow_card_sub_one_eq_one a ha0,
        FiniteField.pow_card_sub_one_eq_one a⁻¹ (inv_ne_zero ha0)]
  have hne : (τ : Matrix (Fin 3) (Fin 3) K) * E ≠ E * τ := by
    rw [hτE, hEτ]
    intro h
    have h02 := congrFun (congrFun h 0) 2
    simp only [hE, eij, Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul,
      mul_one] at h02
    apply ha1
    have hsq : (a + 1) * (a + 1) = 0 := by
      have : a * a = 1 := by
        calc a * a = a * a⁻¹ := by rw [← h02]
          _ = 1 := mul_inv_cancel₀ ha0
      rw [show (a + 1) * (a + 1) = a * a + 2 * a + 1 by ring, this, h2, zero_mul, add_zero,
        one_add_one_eq_two, h2]
    have h0 : a + 1 = 0 := mul_self_eq_zero.mp hsq
    calc a = a + (1 + 1) := by rw [one_add_one_eq_two, h2, add_zero]
      _ = (a + 1) + 1 := by ring
      _ = 1 := by rw [h0, zero_add]
  have huu : unipOf h2 E hEE * unipOf h2 E hEE = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, one_add_mul_self h2 hEE]
    rfl
  refine hasWit_of_sl h2 τ hm hτm hEE ?_ ?_ hne ?_ ?_
  · rw [hEτ, smul_mul_assoc, hEE, smul_zero]
  · rw [hEτ', smul_mul_assoc, hEE, smul_zero]
  · refine antiW_fix (torus3_inv a ha0) fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hτ, coe_torus3, hσa, map_inv₀, Equiv.swap_apply_def]
  · refine antiW_fix (inv_eq_of_mul_eq_one_right huu) fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [hE, eij, Equiv.swap_apply_def]

theorem exists_frobenius_fixed_ne_one [Finite K] {σ : K ≃+* K} {t : ℕ} (hK : Nat.card K = t * t)
    (hK8 : 8 ≤ Nat.card K) (hσ : ∀ x, σ x = x ^ t) (hσσ : ∀ x, σ (σ x) = x) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Fintype.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units]
  refine ⟨(g : K) * σ g, mul_ne_zero g.ne_zero ((map_ne_zero σ).mpr g.ne_zero), ?_, ?_⟩
  · intro h1
    have hgt : g ^ (t + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_succ, ← hσ, mul_comm, h1, Units.val_one]
    have hdvd : Fintype.card K - 1 ∣ t + 1 := hord ▸ orderOf_dvd_of_pow_eq_one hgt
    have hle := Nat.le_of_dvd (by omega) hdvd
    rw [Nat.card_eq_fintype_card] at hK hK8
    rw [hK] at hle hK8
    rcases Nat.lt_or_ge t 3 with ht | ht
    · interval_cases t <;> omega
    · have : 3 * t ≤ t * t := Nat.mul_le_mul_right t ht
      omega
  · rw [map_mul, hσσ, mul_comm]

theorem graphField3WitInput : GraphField3WitInput := by
  intro K _ _ h2 hK8 A σ hσ hα
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hf : 1 ≤ (f : ℕ) := f.2
  obtain ⟨hfe, hσpow, H, hH⟩ :=
    odd_linear_graph_field_involution_conjugacy Nat.prime_two hf hKf le_rfl A σ hσ hα
  have hα' := hα
  rw [sq_conjAut_fieldAut_dualAut] at hα'
  obtain ⟨hσσ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _ hα'
  have hσσx : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσσ
    exact this
  obtain ⟨-, -, H', hH'⟩ := odd_linear_graph_field_involution_conjugacy Nat.prime_two hf hKf
    le_rfl antiW σ hσ (sq_antiW_fieldAut_dualAut hσσ)
  obtain ⟨e, he⟩ := hfe
  have hKt : Nat.card K = 2 ^ e * 2 ^ e := by rw [hKf, he, pow_add]
  have hσt : ∀ x, σ x = x ^ 2 ^ e := fun x => by
    rw [hσpow, show (f : ℕ) / 2 = e by omega]
  obtain ⟨a, ha0, ha1, hσa⟩ := exists_frobenius_fixed_ne_one hKt hK8 hσt hσσx
  have key : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K =
      (conjAut 3 K H * (conjAut 3 K H')⁻¹) *
        (conjAut 3 K antiW * fieldAut 3 K σ * dualAut 3 K) *
          (conjAut 3 K H * (conjAut 3 K H')⁻¹)⁻¹ := by
    rw [hH, hH']
    group
  rw [key]
  exact (hasWit_antiW h2 ha0 ha1 hσa).conj _

end CFSG.ComponentClassification.HarrisLit.L33.C2
