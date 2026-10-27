module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLD

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Matrix
open scoped commutatorElement

theorem conj_mem_commutator_self {G : Type} [Group G] {H : Subgroup G} {g x : G} (hg : g ∈ H)
    (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  have h1 : conjSub g ⁅H, H⁆ = ⁅H, H⁆ := by
    unfold conjSub
    rw [Subgroup.map_commutator]
    have : H.map (MulAut.conj g).toMonoidHom = H := conjSub_eq_self_of_mem hg
    rw [this]
  have := conj_mem_conjSub (n := g) hx
  rwa [h1] at this

theorem perm_matrix_facts : det3 !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1 ∧
    det3 !![0, 1, 0; 1, 0, 0; 0, 0, 1] = 1 ∧
    (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1 ∧
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] = 1 ∧
    ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] * !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
        !![0, 1, 0; 1, 0, 0; 0, 0, 1]) ^ 3 = 1 ∧
    (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] * !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
        !![0, 1, 0; 1, 0, 0; 0, 0, 1] ≠ 1 := by
  decide

theorem aperm_zero_mul (A B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    aperm A 0 * aperm B 0 = aperm (A * B) 0 := by
  rw [aperm_mul, mulVec_zero, add_zero]

theorem aperm_zero_pow (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (k : ℕ) :
    aperm A 0 ^ k = aperm (A ^ k) 0 := by
  induction k with
  | zero => rw [pow_zero, pow_zero, aperm_one_zero]
  | succ k ih => rw [pow_succ, ih, aperm_zero_mul, ← pow_succ]

theorem agl32_perfect : ⁅agl32, agl32⁆ = agl32 := by
  have hle : ⁅agl32, agl32⁆ ≤ agl32 := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact agl32.mul_mem (agl32.mul_mem (agl32.mul_mem ha hb) (agl32.inv_mem ha)) (agl32.inv_mem hb)
  refine agl32_normal_not_two hle (fun g hg x hx => conj_mem_commutator_self hg hx) ?_
  intro h2
  obtain ⟨d1, d2, i1, i2, c3, c1⟩ := perm_matrix_facts
  set P := slOf _ d1
  set P' := slOf _ d2
  have hP : P⁻¹ = P := inv_eq_of_mul_eq_one_right (Subtype.ext i1)
  have hP' : P'⁻¹ = P' := inv_eq_of_mul_eq_one_right (Subtype.ext i2)
  have hc : aperm (P * P' * P * P') 0 ∈ ⁅agl32, agl32⁆ := by
    have := Subgroup.commutator_mem_commutator (aperm_mem_agl32 P 0) (aperm_mem_agl32 P' 0)
    rwa [commutatorElement_def, aperm_inv, aperm_inv, hP, hP', mulVec_zero, mulVec_zero,
      aperm_zero_mul, aperm_zero_mul, aperm_zero_mul] at this
  obtain ⟨k, hk⟩ := h2 ⟨_, hc⟩
  have hk' : aperm (P * P' * P * P') 0 ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : aperm (P * P' * P * P') 0 ^ 3 = 1 := by
    rw [aperm_zero_pow, show (P * P' * P * P') ^ 3 = (1 : Matrix.SpecialLinearGroup (Fin 3)
      (ZMod 2)) from Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact c3),
      aperm_one_zero]
  have hord : orderOf (aperm (P * P' * P * P') 0) = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num)) (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hk')
  rw [orderOf_eq_one_iff, ← aperm_one_zero] at hord
  exact c1 (congrArg Subtype.val (aperm_inj hord).1)

end CFSG.ClassicalInvolution.Q3.TL4
