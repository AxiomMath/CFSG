module

public import CFSG.LieType.Ree.SuzukiBruhatNormalForm

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint
open scoped commutatorElement

variable {a : ℕ} {K : Type} [Field K]

theorem suzuki_unipotents_in_derived (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : suzukiU a K ≤ commutator (suzukiGroup a K) := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcard : 1 < Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨l, hl⟩ := exists_ne (1 : Kˣ)
  have hbij := (suzuki_frobenius_exponents a K hK).2.2.2.2.2.2.2.2.2.2.1
  have hlθ : (l : K) ^ (2 ^ (a + 1) + 1) + 1 ≠ 0 := by
    intro h
    have h1 : (l : K) ^ (2 ^ (a + 1) + 1) = 1 := by linear_combination h - h2
    apply hl
    refine hbij.1 (Units.ext ?_)
    simp only [one_zpow, Units.val_one]
    rw [show (2 ^ (a + 1) + 1 : ℤ) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
      Units.val_pow_eq_pow_val, h1]
  have hl1 : (l : K) + 1 ≠ 0 := by
    intro h
    apply hl
    refine Units.ext ?_
    rw [Units.val_one]
    linear_combination h - h2
  have hcomm : ∀ g h : suzukiGroup a K, ⁅g, h⁆ ∈ commutator (suzukiGroup a K) := fun g h =>
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
  have hZ : ∀ z : K, suzukiSElt a K 0 z ∈ commutator (suzukiGroup a K) := by
    intro z
    have e : ⁅(suzukiDElt a K l)⁻¹, suzukiSElt a K 0 (z / ((l : K) ^ (2 ^ (a + 1) + 1) + 1))⁆ =
        suzukiSElt a K 0 z := by
      rw [commutatorElement_def, inv_inv, suzukiDElt_conj hK, suzukiSElt_inv hK,
        suzukiSElt_mul hK]
      congr 1
      · ring
      · simp only [mul_zero, add_zero]
        field_simp
        ring
    rw [← e]
    exact hcomm _ _
  intro g hg
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
  set c := u / ((l : K) + 1) with hc
  obtain ⟨w, hw⟩ : ∃ w, ⁅(suzukiDElt a K l)⁻¹, suzukiSElt a K c 0⁆ = suzukiSElt a K u w := by
    rw [commutatorElement_def, inv_inv, suzukiDElt_conj hK, suzukiSElt_inv hK,
      suzukiSElt_mul hK]
    have hcu : (l : K) * c + c = u := by
      rw [hc]
      field_simp
    exact ⟨_, by rw [hcu]⟩
  have hsplit : suzukiSElt a K u v = suzukiSElt a K u w * suzukiSElt a K 0 (v - w) := by
    rw [suzukiSElt_mul hK]
    congr 1 <;> simp
  rw [hsplit, ← hw]
  exact mul_mem (hcomm _ _) (hZ _)

theorem suzuki_unipotent_normal_generation
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (R : Subgroup (suzukiGroup a K)) (hR : R.Normal) (hUR : suzukiU a K ≤ R) : R = ⊤ := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hS : ∀ u v : K, suzukiSElt a K u v ∈ R := fun u v => hUR (suzukiSElt_mem_suzukiU a K u v)
  have hW : suzukiWElt a K ∈ R := by
    obtain ⟨-, hfac⟩ := suzuki_bruhat_factorization hK (0 : K) 1 (by simp)
    have hN : ((1 : Kˣ) : K) = suzukiN a 0 1 := by
      simp [suzukiN, zero_pow (by positivity : 2 ^ (a + 1) + 2 ≠ 0)]
    have e : suzukiWElt a K * suzukiSElt a K 0 1 * suzukiWElt a K =
        suzukiSElt a K (1 / ((1 : Kˣ) : K)) (0 / ((1 : Kˣ) : K)) *
          suzukiDElt a K ((1 : Kˣ) ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiWElt a K *
          suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + 1) / ((1 : Kˣ) : K))
            (1 / ((1 : Kˣ) : K) ^ 2 ^ (a + 1)) :=
      suzukiSElt_ext (hfac 1 hN)
    rw [one_zpow, suzukiDElt_one, mul_one] at e
    have hWeq : suzukiWElt a K =
        (suzukiSElt a K (1 / ((1 : Kˣ) : K)) (0 / ((1 : Kˣ) : K)))⁻¹ *
          (suzukiWElt a K * suzukiSElt a K 0 1 * (suzukiWElt a K)⁻¹) *
          (suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + 1) / ((1 : Kˣ) : K))
            (1 / ((1 : Kˣ) : K) ^ 2 ^ (a + 1)))⁻¹ := by
      rw [suzukiWElt_inv, e]
      group
    rw [hWeq]
    exact mul_mem (mul_mem (inv_mem (hS _ _)) (hR.conj_mem _ (hS 0 1) _)) (inv_mem (hS _ _))
  have hD : ∀ l : Kˣ, suzukiDElt a K l ∈ R := by
    intro l
    obtain ⟨-, ⟨φ, hφ⟩, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
    obtain ⟨t, rfl⟩ := hbij.2 l
    set v := φ.symm (t : K) with hv
    have hvt : v ^ 2 ^ (a + 1) = t := by rw [← hφ, hv, RingEquiv.apply_symm_apply]
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, zero_pow hθ0] at hvt
      exact t.ne_zero hvt.symm
    obtain ⟨-, hfac⟩ := suzuki_bruhat_factorization hK (0 : K) v (by simp [hv0])
    have hN : (t : K) = suzukiN a 0 v := by
      simp [suzukiN, hvt]
    have e : suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K =
        suzukiSElt a K (v / (t : K)) (0 / (t : K)) *
          suzukiDElt a K (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiWElt a K *
          suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + v) / (t : K)) (v / (t : K) ^ 2 ^ (a + 1)) :=
      suzukiSElt_ext (hfac t hN)
    have hDeq : suzukiDElt a K (t ^ (2 - 2 ^ (a + 1) : ℤ)) =
        (suzukiSElt a K (v / (t : K)) (0 / (t : K)))⁻¹ *
          (suzukiWElt a K * suzukiSElt a K 0 v * (suzukiWElt a K)⁻¹) *
          (suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + v) / (t : K))
            (v / (t : K) ^ 2 ^ (a + 1)))⁻¹ * (suzukiWElt a K)⁻¹ := by
      rw [suzukiWElt_inv, e]
      group
      rw [mul_assoc, suzukiWElt_mul_self, mul_one]
    rw [hDeq]
    exact mul_mem (mul_mem (mul_mem (inv_mem (hS _ _)) (hR.conj_mem _ (hS 0 v) _))
      (inv_mem (hS _ _))) (inv_mem hW)
  refine eq_top_iff.2 fun g _ => ?_
  rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
  · exact mul_mem (hS u v) (hD l)
  · exact mul_mem (mul_mem (mul_mem (hS u v) (hD l)) hW) (hS c d)

theorem suzuki_perfect
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    commutator (suzukiGroup a K) = ⊤ ∧ Group.IsPerfect (suzukiGroup a K) := by
  have h := suzuki_unipotent_normal_generation hK _ (Subgroup.commutator_normal _ _)
    (suzuki_unipotents_in_derived ha hK)
  exact ⟨h, ⟨h⟩⟩

end CFSG.LieType.Ree
