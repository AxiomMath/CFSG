module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.OmegaFrame

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter QuadraticMap
open scoped commutatorElement

@[expose] def cyc5 : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 2 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 2 4)

@[expose] def cyc5Seven : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 2 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 2 4)

theorem cyc5Seven_castSucc (k : Fin 6) : cyc5Seven k.castSucc = (cyc5 k).castSucc := by
  revert k
  decide

theorem cyc5Seven_six : cyc5Seven 6 = 6 := by decide

theorem cyc5_pow (m : ℕ) (h : (cyc5 ^ m) 0 = 0) : 5 ∣ m := by
  have h5 : cyc5 ^ 5 = 1 := by decide
  have hm : cyc5 ^ m = cyc5 ^ (m % 5) := by
    conv_lhs => rw [← Nat.div_add_mod m 5, pow_add, pow_mul, h5, one_pow, one_mul]
  rw [hm] at h
  have hlt : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h0 : m % 5 = 0 := by
    interval_cases hr : m % 5
    · rfl
    all_goals exact absurd h (by decide)
  omega

theorem fin_six_exists_ne_ne : ∀ i j : Fin 6, i ≠ j → ∃ m : Fin 6, m ≠ i ∧ m ≠ j := by
  decide

section Signs

variable {K : Type*} [Field K]

theorem eq_zero_of_signs_six (h2 : (2 : K) ≠ 0) (a : Fin 6 → Fin 2) (c : K)
    (h : ∀ m : Fin 6, (-1 : K) ^ (a m : ℕ) = c)
    (h6 : ∏ k : Fin 6, (-1 : K) ^ (a k : ℕ) = c) : a = 0 := by
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination (-1 : K) * h)
  have hone : ∀ x : Fin 2, (-1 : K) ^ (x : ℕ) = 1 → x = 0 := by
    intro x hx
    fin_cases x
    · rfl
    · exact absurd (by simpa using hx) hne
  have hc6 : c ^ 6 = c :=
    calc c ^ 6 = ∏ k : Fin 6, c := by simp
      _ = ∏ k : Fin 6, (-1 : K) ^ (a k : ℕ) := Finset.prod_congr rfl fun k _ => (h k).symm
      _ = c := h6
  have hc1 : c = 1 := by
    have h0 := h 0
    generalize a 0 = x at h0
    fin_cases x
    · simpa using h0.symm
    · exfalso
      have hc : c = -1 := by simpa using h0.symm
      have h66 : (-1 : K) ^ 6 = 1 := by norm_num
      rw [hc, h66] at hc6
      exact hne hc6.symm
  funext k
  exact hone _ (by rw [h k, hc1])

end Signs

namespace EqFrame7

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable (Fr : EqFrame7 Q)

theorem Q_ne_zero (i : Fin 7) : Q (Fr.v i) ≠ 0 := by
  rw [Fr.Q_v]
  exact Fr.ν_ne

theorem v_ne_zero (i : Fin 7) : Fr.v i ≠ 0 := fun h =>
  Fr.Q_ne_zero i (by rw [h, QuadraticMap.map_zero])

theorem polar_v (i j : Fin 7) :
    polar Q (Fr.v i) (Fr.v j) = if i = j then 2 * Fr.ν else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, polar_self_eq_two_mul, Fr.Q_v]
  · rw [if_neg h, Fr.orth i j h]

@[expose] def sgn (K : Type*) [Field K] (i j : Fin 7) : K := if i = j then -1 else 1

theorem reflect_apply_v (i j : Fin 7) : reflect Q (Fr.v i) (Fr.v j) = sgn K i j • Fr.v j := by
  rcases eq_or_ne i j with rfl | h
  · simp [sgn, reflect_apply_self (Fr.Q_ne_zero i)]
  · simp [sgn, h, reflect_apply_of_polar_eq_zero (Fr.orth i j h)]

theorem reflect_comm_v (i j : Fin 7) :
    reflect Q (Fr.v i) * reflect Q (Fr.v j) = reflect Q (Fr.v j) * reflect Q (Fr.v i) := by
  by_cases h : i = j
  · rw [h]
  · exact reflect_comm (Fr.orth i j h)

@[expose] noncomputable def g (k : Fin 6) : V ≃ₗ[K] V :=
  reflect Q (Fr.v k.castSucc) * reflect Q (Fr.v 6)

theorem castSucc_ne_six (k : Fin 6) : k.castSucc ≠ 6 := by
  revert k
  decide

theorem sgn_six_castSucc (m : Fin 6) : sgn K 6 m.castSucc = 1 := by
  simp [sgn, (castSucc_ne_six m).symm]

theorem sgn_castSucc_six (k : Fin 6) : sgn K k.castSucc 6 = 1 := by
  simp [sgn, castSucc_ne_six k]

theorem sgn_six_six : sgn K 6 6 = -1 := by simp [sgn]

theorem sgn_castSucc_castSucc (k m : Fin 6) :
    sgn K k.castSucc m.castSucc = if k = m then -1 else 1 := by
  simp [sgn, Fin.castSucc_inj]

theorem g_apply_v (k : Fin 6) (j : Fin 7) :
    Fr.g k (Fr.v j) = (sgn K 6 j * sgn K k.castSucc j) • Fr.v j := by
  rw [g, LinearEquiv.mul_apply, reflect_apply_v, map_smul, reflect_apply_v, smul_smul]

theorem g_mem (h2 : (2 : K) ≠ 0) (k : Fin 6) :
    Fr.g k ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  reflect_mul_reflect_mem_commutator h2 (Fr.orth _ _ (castSucc_ne_six k))
    (by rw [Fr.Q_v, Fr.Q_v]) (Fr.Q_ne_zero 6)

theorem g_sq (k : Fin 6) : Fr.g k * Fr.g k = 1 := by
  have hc := Fr.reflect_comm_v k.castSucc 6
  calc Fr.g k * Fr.g k
      = reflect Q (Fr.v k.castSucc) * (reflect Q (Fr.v 6) * reflect Q (Fr.v k.castSucc)) *
          reflect Q (Fr.v 6) := by simp only [g, mul_assoc]
    _ = reflect Q (Fr.v k.castSucc) * (reflect Q (Fr.v k.castSucc) * reflect Q (Fr.v 6)) *
          reflect Q (Fr.v 6) := by rw [← hc]
    _ = (reflect Q (Fr.v k.castSucc) * reflect Q (Fr.v k.castSucc)) *
          (reflect Q (Fr.v 6) * reflect Q (Fr.v 6)) := by simp only [mul_assoc]
    _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]

theorem g_comm (i j : Fin 6) : Fr.g i * Fr.g j = Fr.g j * Fr.g i := by
  have hc : ∀ a b : Fin 7, Commute (reflect Q (Fr.v a)) (reflect Q (Fr.v b)) :=
    fun a b => Fr.reflect_comm_v a b
  exact (((hc i.castSucc j.castSucc).mul_right (hc i.castSucc 6)).mul_left
    ((hc 6 j.castSucc).mul_right (hc 6 6)))

theorem g_not_mem_scalars (h2 : (2 : K) ≠ 0) (a : Fin 6 → Fin 2) (ha : a ≠ 0) :
    (List.ofFn fun k => Fr.g k ^ (a k : ℕ)).prod ∉ scalars K V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.1 hmem
  have hj : ∀ j : Fin 7, ∏ k : Fin 6, (sgn K 6 j * sgn K k.castSucc j) ^ (a k : ℕ) = c := by
    intro j
    have h := prod_ofFn_pow_apply (g := Fr.g) (t := Fr.v j)
      (c := fun k => sgn K 6 j * sgn K k.castSucc j) (fun k => Fr.g_apply_v k j)
      (fun k => (a k : ℕ))
    rw [hc (Fr.v j)] at h
    exact (smul_left_injective K (Fr.v_ne_zero j) h).symm
  apply ha
  refine eq_zero_of_signs_six h2 a c (fun m => ?_) ?_
  · rw [← hj m.castSucc, Finset.prod_eq_single m]
    · simp [sgn_six_castSucc, sgn_castSucc_castSucc]
    · intro k _ hk
      simp [sgn_six_castSucc, sgn_castSucc_castSucc, hk]
    · simp
  · rw [← hj 6]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [sgn_six_six, sgn_castSucc_six]

theorem g_mul_g_not_mem_scalars (h2 : (2 : K) ≠ 0) {i j : Fin 6} (hij : i ≠ j) :
    Fr.g i * Fr.g j ∉ scalars K V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.1 hmem
  have hev : ∀ m : Fin 7, (sgn K 6 m * sgn K j.castSucc m) * (sgn K 6 m * sgn K i.castSucc m) =
      c := by
    intro m
    have h := hc (Fr.v m)
    rw [LinearEquiv.mul_apply, g_apply_v, map_smul, g_apply_v, smul_smul] at h
    exact smul_left_injective K (Fr.v_ne_zero m) h
  obtain ⟨m, hmi, hmj⟩ := fin_six_exists_ne_ne i j hij
  have h1 := hev i.castSucc
  have h2' := hev m.castSucc
  simp [sgn_six_castSucc, sgn_castSucc_castSucc, hij, hij.symm, hmi, hmj, Ne.symm hmi,
    Ne.symm hmj] at h1 h2'
  apply h2
  linear_combination h2' - h1

theorem Q_sub {a b : Fin 7} (hab : a ≠ b) : Q (Fr.v a - Fr.v b) = 2 * Fr.ν := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
    Fr.orth a b hab, Fr.Q_v, Fr.Q_v]
  ring

theorem Q_sub_ne_zero (h2 : (2 : K) ≠ 0) {a b : Fin 7} (hab : a ≠ b) :
    Q (Fr.v a - Fr.v b) ≠ 0 := by
  rw [Fr.Q_sub hab]
  exact mul_ne_zero h2 Fr.ν_ne

theorem polar_sub_sub {a b c d : Fin 7} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    polar Q (Fr.v a - Fr.v b) (Fr.v c - Fr.v d) = 0 := by
  rw [polar_sub_left, polar_sub_right, polar_sub_right, Fr.orth _ _ hac, Fr.orth _ _ had,
    Fr.orth _ _ hbc, Fr.orth _ _ hbd]
  ring

theorem reflect_sub_apply (h2 : (2 : K) ≠ 0) {a b : Fin 7} (hab : a ≠ b) (j : Fin 7) :
    reflect Q (Fr.v a - Fr.v b) (Fr.v j) = Fr.v (Equiv.swap a b j) := by
  have hν : (2 * Fr.ν) / (2 * Fr.ν) = 1 := div_self (mul_ne_zero h2 Fr.ν_ne)
  rw [reflect_apply (Fr.Q_sub_ne_zero h2 hab), polar_sub_left, Fr.polar_v, Fr.polar_v,
    Fr.Q_sub hab]
  rcases eq_or_ne j a with rfl | hja
  · rw [Equiv.swap_apply_left, if_pos rfl, if_neg (Ne.symm hab), sub_zero, hν, one_smul]
    abel
  rcases eq_or_ne j b with rfl | hjb
  · rw [Equiv.swap_apply_right, if_neg hja.symm, if_pos rfl, zero_sub, neg_div, hν, neg_smul,
      one_smul, sub_neg_eq_add]
    abel
  · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, if_neg hja.symm, if_neg hjb.symm, sub_zero,
      zero_div, zero_smul, sub_zero]

@[expose] noncomputable def tau : V ≃ₗ[K] V :=
  (reflect Q (Fr.v 0 - Fr.v 2) * reflect Q (Fr.v 3 - Fr.v 4)) *
    (reflect Q (Fr.v 0 - Fr.v 1) * reflect Q (Fr.v 2 - Fr.v 4))

theorem tau_mem_orthogonalGroup : Fr.tau ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _))
    (mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _))

theorem tau_mem (h2 : (2 : K) ≠ 0) :
    Fr.tau ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  mul_mem
    (reflect_mul_reflect_mem_commutator h2
      (Fr.polar_sub_sub (by decide) (by decide) (by decide) (by decide))
      (by rw [Fr.Q_sub (by decide), Fr.Q_sub (by decide)]) (Fr.Q_sub_ne_zero h2 (by decide)))
    (reflect_mul_reflect_mem_commutator h2
      (Fr.polar_sub_sub (by decide) (by decide) (by decide) (by decide))
      (by rw [Fr.Q_sub (by decide), Fr.Q_sub (by decide)]) (Fr.Q_sub_ne_zero h2 (by decide)))

theorem tau_apply_v (h2 : (2 : K) ≠ 0) (j : Fin 7) : Fr.tau (Fr.v j) = Fr.v (cyc5Seven j) := by
  simp only [tau, LinearEquiv.mul_apply, Fr.reflect_sub_apply h2 (show (0 : Fin 7) ≠ 2 by decide),
    Fr.reflect_sub_apply h2 (show (3 : Fin 7) ≠ 4 by decide),
    Fr.reflect_sub_apply h2 (show (0 : Fin 7) ≠ 1 by decide),
    Fr.reflect_sub_apply h2 (show (2 : Fin 7) ≠ 4 by decide), cyc5Seven, Equiv.Perm.mul_apply]

theorem tau_conj (h2 : (2 : K) ≠ 0) (k : Fin 6) : Fr.tau * Fr.g k * Fr.tau⁻¹ = Fr.g (cyc5 k) := by
  have hτ := Fr.tau_mem_orthogonalGroup
  calc Fr.tau * Fr.g k * Fr.tau⁻¹
      = (Fr.tau * reflect Q (Fr.v k.castSucc) * Fr.tau⁻¹) *
          (Fr.tau * reflect Q (Fr.v 6) * Fr.tau⁻¹) := by simp only [g]; group
    _ = reflect Q (Fr.tau (Fr.v k.castSucc)) * reflect Q (Fr.tau (Fr.v 6)) := by
        rw [reflect_conj hτ, reflect_conj hτ]
    _ = Fr.g (cyc5 k) := by
        rw [Fr.tau_apply_v h2, Fr.tau_apply_v h2, cyc5Seven_castSucc, cyc5Seven_six]
        rfl

end EqFrame7

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
