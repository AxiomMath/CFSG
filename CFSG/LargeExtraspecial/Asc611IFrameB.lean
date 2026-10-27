module

public import CFSG.LargeExtraspecial.Asc611IFrame
public import CFSG.LargeExtraspecial.Asc611IStepA

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {r : ℕ} {q : Fin r → Fin m → K}

theorem exists_frame_ext (he : e * e = 1) (F : IsFrame e q) {z : Fin m → K}
    (hz : herm frob z (invN e z) = 1) (hqz : ∀ i, herm frob (q i) (invN e z) = 0) :
    ∃ z' : Fin m → K, invN e z' = invN e z ∧ herm frob z' z' = 0 ∧
      ∀ i, herm frob (q i) z' = 0 := by
  set w := ∑ l, herm frob (q l) z • invN e (q l) with hw
  have hw0 : invN e w = 0 := by
    rw [hw, invN_sum]
    simp only [invN_smul, invN_invN he, smul_zero, Finset.sum_const_zero]
  set z₁ := z + w with hz₁
  have hNz₁ : invN e z₁ = invN e z := by rw [hz₁, invN_add, hw0, add_zero]
  have hqz₁ : ∀ i, herm frob (q i) z₁ = 0 := fun i => by
    rw [hz₁, herm_add_right, hw, F.herm_q_sum, add_self_K]
  obtain ⟨c, hc⟩ := exists_add_frob_eq
    ((frob_eq_self_iff _).1 (herm_self_fixed frob frob_frob z₁))
  have hz₁N : herm frob z₁ (invN e z) = 1 := by
    rw [hz₁, herm_add_left, hz, hw, herm_sum_left']
    simp only [herm_smul_left, herm_invN_invN he, mul_zero, Finset.sum_const_zero, add_zero]
  have hNzz₁ : herm frob (invN e z) z₁ = 1 := by
    rw [herm_conj frob frob_frob, hz₁N, map_one]
  clear_value z₁
  refine ⟨z₁ + c • invN e z, ?_, ?_, fun i => ?_⟩
  · rw [invN_add, hNz₁, invN_smul, invN_invN he, smul_zero, add_zero]
  · rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_right,
      herm_smul_right, herm_smul_left, hz₁N, hNzz₁, herm_invN_invN he]
    linear_combination hc + herm frob z₁ z₁ * two_eq_zero
  · rw [herm_add_right, hqz₁, herm_smul_right, hqz, mul_zero, add_zero]

theorem invN_eq_sum_of_frame (he : e * e = 1) (F : IsFrame e q)
    (hno : ∀ z, (∀ i, herm frob (q i) (invN e z) = 0) → herm frob z (invN e z) = 0)
    (x : Fin m → K) : invN e x = ∑ l, herm frob (invN e (q l)) x • invN e (q l) := by
  set P : (Fin m → K) → (Fin m → K) := fun b => b + ∑ l, herm frob (q l) (invN e b) • q l
    with hPdef
  have hP : ∀ b i, herm frob (q i) (invN e (P b)) = 0 := by
    intro b i
    rw [hPdef, invN_add, invN_sum, herm_add_right, herm_sum_right']
    simp only [invN_smul, herm_smul_right, F.orth, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact add_self_K _
  have hHc : ∀ x z : Fin m → K, herm frob z (invN e x) = frob (herm frob x (invN e z)) :=
    fun x z => herm_invN_swap he x z
  have hPP : ∀ b b', herm frob (P b) (invN e (P b')) = 0 := by
    intro b b'
    have key : ∀ l : K, l ≠ 0 → 0 + l * herm frob (P b) (invN e (P b')) +
        frob l * herm frob (P b') (invN e (P b)) = 0 := by
      intro l _
      have hz := hno (P b + l • P b') (fun i => by
        rw [invN_add, invN_smul, herm_add_right, herm_smul_right, hP, hP, mul_zero, add_zero])
      rw [(isSesq_H e).expand, hno _ (hP b), hno _ (hP b'), mul_zero, add_zero] at hz
      linear_combination hz
    exact (three_lambda key).1
  have hPx : invN e (P x) = 0 := by
    refine eq_zero_of_herm frob fun b => ?_
    rw [herm_invN_left he]
    have hb : b = P b + ∑ l, herm frob (q l) (invN e b) • q l := by
      rw [hPdef]
      simp only [add_assoc, vec_add_self, add_zero]
    rw [hb, invN_add, herm_add_right, hPP, zero_add, invN_sum, herm_sum_right']
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [invN_smul, herm_smul_right, hHc (q l) (P x), hP, map_zero, mul_zero]
  have h1 := hPx
  rw [hPdef, invN_add, invN_sum] at h1
  simp only [invN_smul] at h1
  have h2 := congrArg (· + ∑ l, herm frob (q l) (invN e x) • invN e (q l)) h1
  simp only [add_assoc, vec_add_self, add_zero, zero_add] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [herm_invN_left he]

theorem actsBy_one_e (he : e * e = 1) (F : IsFrame e q)
    (hno : ∀ z, (∀ i, herm frob (q i) (invN e z) = 0) → herm frob z (invN e z) = 0) :
    ActsBy e q 1 e := fun x => by
  rw [smul_eq_invN_add, invN_eq_sum_of_frame he F hno x, add_comm]
  congr 1
  unfold frameMap
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end CFSG.LargeExtraspecial.Asc611I
