module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalDefs
import CFSG.ClassicalInvolution.Generic.QuadraticNorm

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open scoped MatrixGroups
open Matrix CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {K : Type} [Field K]

@[expose] def cardMinusPi (q : ℕ) : ℕ := if q % 3 = 1 then q - 1 else q + 1

@[expose] def cardPlusPi (q : ℕ) : ℕ := if q % 3 = 1 then q + 1 else q - 1

theorem not_dvd_cardMinusPi_of_dvd_cardPlusPi {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (h : p ∣ cardPlusPi q) : ¬ p ∣ cardMinusPi q := by
  intro h'
  have h2 : p ∣ 2 := by
    unfold cardPlusPi cardMinusPi at *
    split_ifs at h h' with hq3
    · have := Nat.dvd_sub h h'
      have e : q + 1 - (q - 1) = 2 := by omega
      rwa [e] at this
    · have := Nat.dvd_sub h' h
      have e : q + 1 - (q - 1) = 2 := by omega
      rwa [e] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem dvd_mul_sq_sub_one_of_dvd_cardPlusPi {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ cardPlusPi q) :
    p ∣ q * (q ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ q
  have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  unfold cardPlusPi at h
  split_ifs at h
  · rw [e]; exact Dvd.dvd.mul_right h _
  · rw [e]; exact Dvd.dvd.mul_left h _

theorem cast_sub_eq_cardMinusPi {q : ℕ} (hq : 1 ≤ q) (h3 : ¬ 3 ∣ q) {η : ℤ}
    (hη : η = 1 ∨ η = -1) (hdvd : (3 : ℤ) ∣ (q : ℤ) - η) :
    (q : ℤ) - η = (cardMinusPi q : ℤ) := by
  unfold cardMinusPi
  rcases hη with rfl | rfl <;> split_ifs with h <;> push_cast [Nat.cast_sub hq] <;> omega

theorem not_three_dvd_natCard [Finite K] (h3 : (3 : K) ≠ 0) : ¬ 3 ∣ Nat.card K := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 3 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h0 : (3 : K) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, nsmul_eq_mul] at this
    simpa using this
  exact h3 ((mul_eq_zero.mp h0).resolve_right hx0)

@[expose] def cubeRootSL (K : Type) [Field K] : SL(2, K) :=
  ⟨cubeRootMat K, by simp [cubeRootMat, Matrix.det_fin_two_of]⟩

theorem coe_cubeRootSL : ((cubeRootSL K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = cubeRootMat K :=
  rfl

@[expose] def torusSL (K : Type) [Field K] : Subgroup SL(2, K) :=
  Subgroup.centralizer {cubeRootSL K}

theorem mem_torusSL_iff {t : SL(2, K)} :
    t ∈ torusSL K ↔ (t : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (t : Matrix (Fin 2) (Fin 2) K) := by
  rw [torusSL, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cubeRootSL] at this
    exact this
  · intro h
    exact sl_ext (by simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cubeRootSL]; exact h)

theorem cubeRootSL_mem_torusSL : cubeRootSL K ∈ torusSL K := by
  rw [mem_torusSL_iff]
  rfl

theorem orderOf_cubeRootSL : orderOf (cubeRootSL K) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact cubeRootMat_pow_three
  · intro h
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [cubeRootSL, cubeRootMat] at this

private noncomputable def torusA (K : Type) [Field K] (h3 : (3 : K) ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -2; 2, -1] (by
    simp [Matrix.det_fin_two_of]
    intro h
    apply h3
    linear_combination h)

private theorem coe_torusA (h3 : (3 : K) ≠ 0) :
    ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, -2; 2, -1] := rfl

private theorem coe_torusA_eq (h3 : (3 : K) ≠ 0) :
    ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 + (2 : K) • cubeRootMat K := by
  rw [coe_torusA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeRootMat] <;> ring

private theorem coe_torusA_mul_self (h3 : (3 : K) ≠ 0) :
    ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_torusA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private def unipotentSL (K : Type) [Field K] : SL(2, K) := ⟨!![1, 1; 0, 1], by simp⟩

private theorem isInvolDiag_torusA (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsInvolDiag (torusA K h3) := by
  have hAA := coe_torusA_mul_self h3
  have h3' : (-3 : K) ≠ 0 := neg_ne_zero.mpr h3
  refine ⟨fun s => ?_, ⟨unipotentSL K, ?_⟩⟩
  · have h1 := (slConj_eq_iff (torusA K h3) s (slConjugation 2 K (torusA K h3) s)).1 rfl
    rw [slConj_eq_iff]
    set A : Matrix (Fin 2) (Fin 2) K := ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    have hu : A * ((-3 : K)⁻¹ • A) = 1 := by
      rw [mul_smul_comm, hAA, smul_smul, inv_mul_cancel₀ h3', one_smul]
    calc A * ((slConjugation 2 K (torusA K h3) s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        = A * ((slConjugation 2 K (torusA K h3) s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
            (A * ((-3 : K)⁻¹ • A)) := by rw [hu, mul_one]
      _ = (A * (((slConjugation 2 K (torusA K h3) s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * A)) *
            ((-3 : K)⁻¹ • A) := by simp only [Matrix.mul_assoc]
      _ = (A * (A * (s : Matrix (Fin 2) (Fin 2) K))) * ((-3 : K)⁻¹ • A) := by rw [← h1]
      _ = ((A * A) * (s : Matrix (Fin 2) (Fin 2) K)) * ((-3 : K)⁻¹ • A) := by
          simp only [Matrix.mul_assoc]
      _ = (s : Matrix (Fin 2) (Fin 2) K) * A := by
          rw [hAA, smul_mul_assoc, Matrix.one_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
            mul_inv_cancel₀ h3', one_smul]
  · intro h
    rw [slConj_eq_iff] at h
    have h00 := congrFun (congrFun h 0) 0
    simp [coe_torusA, unipotentSL, Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact h2 h00

private theorem fixSub_torusA_eq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    fixSub (torusA K h3) = torusSL K := by
  ext t
  rw [mem_fixSub_iff_comm, mem_torusSL_iff]
  show ((torusA K h3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * _ = _ * _ ↔ _
  rw [coe_torusA_eq h3]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, add_right_inj]
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => (2 : K)⁻¹ • M) h
    simpa [smul_smul, inv_mul_cancel₀ h2] using h'.symm
  · intro h
    rw [h]

theorem card_torusSL [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) :
    Nat.card (torusSL K) = cardMinusPi (Nat.card K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hA := isInvolDiag_torusA h2 h3
  have hodd : Odd (Nat.card K) := by
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  rw [← fixSub_torusA_eq h2 h3]
  obtain ⟨-, η, hη, hcard⟩ := hA.isCyclic_and_card_fixSub hodd
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hmem : cubeRootSL K ∈ fixSub (torusA K h3) := by
    rw [fixSub_torusA_eq h2 h3]
    exact cubeRootSL_mem_torusSL
  have hdvd3 : 3 ∣ Nat.card (fixSub (torusA K h3)) := by
    have := orderOf_dvd_natCard (⟨cubeRootSL K, hmem⟩ : fixSub (torusA K h3))
    rwa [Subgroup.orderOf_mk, orderOf_cubeRootSL] at this
  have hdvdZ : (3 : ℤ) ∣ (Nat.card K : ℤ) - η := by
    rw [← hcard]
    exact_mod_cast hdvd3
  exact_mod_cast hcard.trans (cast_sub_eq_cardMinusPi hq (not_three_dvd_natCard h3) hη hdvdZ)

theorem exists_mem_torusSL_orderOf_eq [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ cardMinusPi (Nat.card K)) :
    ∃ t : SL(2, K), t ∈ torusSL K ∧ orderOf t = p := by
  haveI := Fact.mk hp
  rw [← card_torusSL hK h3] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

theorem eq_one_of_mem_torusSL_of_pow_eq_one [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ cardMinusPi (Nat.card K)) {t : SL(2, K)}
    (ht : t ∈ torusSL K) (hpow : t ^ p = 1) : t = 1 := by
  have h1 : orderOf t ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf t ∣ cardMinusPi (Nat.card K) := by
    rw [← card_torusSL hK h3]
    have := orderOf_dvd_natCard (⟨t, ht⟩ : torusSL K)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hndvd

theorem exists_gl_commute_cubeRootMat_orderOf_eq [Finite K] (hK : ringChar K ≠ 2)
    (h3 : (3 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ cardMinusPi (Nat.card K)) :
    ∃ s : GL (Fin 2) K, (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (s : Matrix (Fin 2) (Fin 2) K) ∧
        (s : Matrix (Fin 2) (Fin 2) K).det = 1 ∧ orderOf s = p := by
  obtain ⟨t, ht, hto⟩ := exists_mem_torusSL_orderOf_eq hK h3 hp hdvd
  refine ⟨Matrix.SpecialLinearGroup.toGL t, ?_, ?_, ?_⟩
  · simpa using mem_torusSL_iff.1 ht
  · simpa using t.2
  · rw [← hto]
    exact orderOf_injective (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K)
      (fun a b h => Subtype.ext (congrArg Units.val h)) t

private def slOfDet (s : Matrix (Fin 2) (Fin 2) K) (hdet : s.det = 1) : SL(2, K) := ⟨s, hdet⟩

theorem eq_one_of_commute_cubeRootMat_of_pow_eq_one [Finite K] (hK : ringChar K ≠ 2)
    (h3 : (3 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ cardMinusPi (Nat.card K))
    {s : Matrix (Fin 2) (Fin 2) K} (hs : s * cubeRootMat K = cubeRootMat K * s)
    (hdet : s.det = 1) (hpow : s ^ p = 1) : s = 1 := by
  have ht : slOfDet s hdet ∈ torusSL K := mem_torusSL_iff.2 hs
  have h1 := eq_one_of_mem_torusSL_of_pow_eq_one hK h3 hp hndvd ht (sl_ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hpow))
  exact congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h1

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
