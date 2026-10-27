module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private def sl23i : SL23 := ⟨!![0, -1; 1, 0], by decide⟩

private def sl23j : SL23 := ⟨!![1, 1; 1, -1], by decide⟩

private def sl23c : SL23 := ⟨!![1, 1; 0, 1], by decide⟩

private def q8T (A B x : SL23) : SL23 :=
  if x = 1 then 1
  else if x = -1 then -1
  else if x = sl23i then A
  else if x = -sl23i then -A
  else if x = sl23j then B
  else if x = -sl23j then -B
  else if x = sl23i * sl23j then A * B
  else if x = -(sl23i * sl23j) then -(A * B)
  else 1

private theorem q8T_i_apply : ∀ A B : SL23, q8T A B sl23i = A := by decide +kernel

private theorem q8T_neg_i_apply : ∀ A B : SL23, q8T A B (-sl23i) = -A := by decide +kernel

private theorem q8T_j_apply : ∀ A B : SL23, q8T A B sl23j = B := by decide +kernel

private theorem q8T_neg_j_apply : ∀ A B : SL23, q8T A B (-sl23j) = -B := by decide +kernel

private theorem q8T_k_apply : ∀ A B : SL23, q8T A B (sl23i * sl23j) = A * B := by
  decide +kernel

private theorem q8T_neg_k_apply : ∀ A B : SL23, q8T A B (-(sl23i * sl23j)) = -(A * B) := by
  decide +kernel

private theorem q8T_id (x : SL23) (hx : x ^ 4 = 1) : q8T sl23i sl23j x = x :=
  (by decide +kernel : ∀ x : SL23, x ^ 4 = 1 → q8T sl23i sl23j x = x) x hx

private theorem sl23_q8_mem_dichotomy (x : SL23) (hx : x ^ 4 = 1) :
    x = 1 ∨ x = -1 ∨ x = sl23i ∨ x = -sl23i ∨ x = sl23j ∨ x = -sl23j ∨
      x = sl23i * sl23j ∨ x = -(sl23i * sl23j) :=
  (by decide +kernel : ∀ y : SL23, y ^ 4 = 1 →
    y = 1 ∨ y = -1 ∨ y = sl23i ∨ y = -sl23i ∨ y = sl23j ∨ y = -sl23j ∨
      y = sl23i * sl23j ∨ y = -(sl23i * sl23j)) x hx

private theorem sl23_q8_invol_fixes :
    ∀ A B : SL23, A ^ 4 = 1 → B ^ 4 = 1 →
      q8T A B A = sl23i → q8T A B B = sl23j →
      q8T A B sl23i ≠ -sl23i → q8T A B sl23j ≠ -sl23j →
      q8T A B (sl23i * sl23j) ≠ -(sl23i * sl23j) →
      A = sl23i ∧ B = sl23j := by
  decide +kernel

private theorem sl23_decomp (m : SL23) :
    ∃ e : Fin 3, ∃ x : SL23, x ^ 4 = 1 ∧ m = sl23c ^ (e : ℕ) * x :=
  (by decide +kernel : ∀ m : SL23,
    ∃ e : Fin 3, ∃ x : SL23, x ^ 4 = 1 ∧ m = sl23c ^ (e : ℕ) * x) m

private theorem sl23_centralizer_q8 (y : SL23) (hi : y * sl23i = sl23i * y)
    (hj : y * sl23j = sl23j * y) : y = 1 ∨ y = -1 :=
  (by decide +kernel : ∀ y : SL23, y * sl23i = sl23i * y → y * sl23j = sl23j * y →
    y = 1 ∨ y = -1) y hi hj

private theorem sl23_c_conj_q8 (x : SL23) (hx : x ^ 4 = 1) :
    (sl23c * x * sl23c⁻¹) ^ 4 = 1 :=
  (by decide +kernel : ∀ x : SL23, x ^ 4 = 1 → (sl23c * x * sl23c⁻¹) ^ 4 = 1) x hx

private theorem sl23_dichotomy (φ : SL23 →* SL23) (hφ : ∀ m, φ (φ m) = m) :
    (∀ m, φ m = m) ∨ ∃ m, φ m = m * (-1) := by
  by_cases hex : ∃ m, φ m = m * (-1)
  · exact Or.inr hex
  · left
    push Not at hex
    have hneg1 : φ (-1) = -1 := by
      have hsq : φ (-1) * φ (-1) = 1 := by
        rw [← map_mul, show (-1 : SL23) * (-1) = 1 by decide, map_one]
      rcases sl23_unique_involution _ hsq with h | h
      · exact absurd h (fun h1 => hex (-1) (by rw [h1]; decide))
      · exact h
    have hneg_phi : ∀ y, φ (-y) = -(φ y) := by
      intro y
      rw [← mul_neg_one y, map_mul, hneg1, mul_neg_one]
    let A : SL23 := φ sl23i
    let B : SL23 := φ sl23j
    have hA4 : A ^ 4 = 1 := by
      change (φ sl23i) ^ 4 = 1
      rw [← map_pow, show sl23i ^ 4 = 1 by decide, map_one]
    have hB4 : B ^ 4 = 1 := by
      change (φ sl23j) ^ 4 = 1
      rw [← map_pow, show sl23j ^ 4 = 1 by decide, map_one]
    have hq8T : ∀ x : SL23, x ^ 4 = 1 → φ x = q8T A B x := by
      intro x hx
      rcases sl23_q8_mem_dichotomy x hx with h | h | h | h | h | h | h | h
      · rw [h]; simp [q8T]
      · rw [h, hneg1]; simp [q8T]
      · rw [h, q8T_i_apply A B]
      · rw [h, hneg_phi, q8T_neg_i_apply A B]
      · rw [h, q8T_j_apply A B]
      · rw [h, hneg_phi, q8T_neg_j_apply A B]
      · rw [h, map_mul, q8T_k_apply A B]
      · rw [h, hneg_phi, map_mul, q8T_neg_k_apply A B]
    have hAi : q8T A B A = sl23i := by
      have h := hφ sl23i
      change φ A = sl23i at h
      rwa [hq8T A hA4] at h
    have hBj : q8T A B B = sl23j := by
      have h := hφ sl23j
      change φ B = sl23j at h
      rwa [hq8T B hB4] at h
    have hposi : q8T A B sl23i ≠ -sl23i := by
      rw [q8T_i_apply A B]
      intro hcon
      apply hex sl23i
      change A = sl23i * (-1)
      rw [mul_neg_one]
      exact hcon
    have hposj : q8T A B sl23j ≠ -sl23j := by
      rw [q8T_j_apply A B]
      intro hcon
      apply hex sl23j
      change B = sl23j * (-1)
      rw [mul_neg_one]
      exact hcon
    have hposk : q8T A B (sl23i * sl23j) ≠ -(sl23i * sl23j) := by
      rw [q8T_k_apply A B]
      intro hcon
      apply hex (sl23i * sl23j)
      rw [map_mul, mul_neg_one]
      exact hcon
    obtain ⟨hAeq, hBeq⟩ := sl23_q8_invol_fixes A B hA4 hB4 hAi hBj hposi hposj hposk
    have hfixq8 : ∀ x : SL23, x ^ 4 = 1 → φ x = x := by
      intro x hx
      rw [hq8T x hx, hAeq, hBeq, q8T_id x hx]
    have hy_eq : ∀ x : SL23, x ^ 4 = 1 →
        (sl23c⁻¹ * φ sl23c) * x = x * (sl23c⁻¹ * φ sl23c) := by
      intro x hx
      have h1 : φ (sl23c * x * sl23c⁻¹) = sl23c * x * sl23c⁻¹ := hfixq8 _ (sl23_c_conj_q8 x hx)
      have h2 : φ (sl23c * x * sl23c⁻¹) = φ sl23c * x * (φ sl23c)⁻¹ := by
        simp only [map_mul, map_inv, hfixq8 x hx]
      have heq : φ sl23c * x * (φ sl23c)⁻¹ = sl23c * x * sl23c⁻¹ := by
        rw [← h2]; exact h1
      have hy : (sl23c⁻¹ * φ sl23c) * x * (sl23c⁻¹ * φ sl23c)⁻¹ = x := by
        calc (sl23c⁻¹ * φ sl23c) * x * (sl23c⁻¹ * φ sl23c)⁻¹
            = sl23c⁻¹ * (φ sl23c * x * (φ sl23c)⁻¹) * sl23c := by group
          _ = sl23c⁻¹ * (sl23c * x * sl23c⁻¹) * sl23c := by rw [heq]
          _ = x := by group
      calc (sl23c⁻¹ * φ sl23c) * x
          = ((sl23c⁻¹ * φ sl23c) * x * (sl23c⁻¹ * φ sl23c)⁻¹) *
              (sl23c⁻¹ * φ sl23c) := by group
        _ = x * (sl23c⁻¹ * φ sl23c) := by rw [hy]
    have hyval : (sl23c⁻¹ * φ sl23c) = 1 ∨ (sl23c⁻¹ * φ sl23c) = -1 :=
      sl23_centralizer_q8 _ (hy_eq sl23i (by decide)) (hy_eq sl23j (by decide))
    have hphi_c : φ sl23c = sl23c := by
      have hcy : sl23c * (sl23c⁻¹ * φ sl23c) = φ sl23c := by group
      rcases hyval with hy1 | hym1
      · rw [hy1, mul_one] at hcy; exact hcy.symm
      · exfalso
        exact hex sl23c (by rw [← hcy, hym1])
    intro m
    obtain ⟨e3, x, hx4, hm⟩ := sl23_decomp m
    rw [hm, map_mul, map_pow, hphi_c, hfixq8 x hx4]

theorem sec10T_sl23_involution {K : Subgroup G}
    (hK : Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) {z s : G} (hzK : z ∈ K)
    (hz2 : orderOf z = 2) (hs2 : s * s = 1) (hsz : s * z = z * s)
    (hsK : ∀ x ∈ K, s * x * s⁻¹ ∈ K) :
    (∀ k ∈ K, s * k = k * s) ∨ ∃ k ∈ K, k⁻¹ * s * k = s * z := by
  obtain ⟨e⟩ := hK
  let conj : ↥K →* ↥K :=
    { toFun := fun x => ⟨s * (x : G) * s⁻¹, hsK x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hconj2 : ∀ x : ↥K, conj (conj x) = x := by
    intro x
    apply Subtype.ext
    have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    change s * (s * (x : G) * s⁻¹) * s⁻¹ = (x : G)
    rw [hs]
    calc s * (s * (x : G) * s) * s = (s * s) * (x : G) * (s * s) := by group
      _ = (x : G) := by rw [hs2]; group
  let φ : SL23 →* SL23 := e.toMonoidHom.comp (conj.comp e.symm.toMonoidHom)
  have hφ_apply : ∀ m : SL23, φ m = e (conj (e.symm m)) := fun m => rfl
  have hφ : ∀ m, φ (φ m) = m := by
    intro m
    rw [hφ_apply (φ m), hφ_apply m, e.symm_apply_apply, hconj2, e.apply_symm_apply]
  have hφe : ∀ x : ↥K, φ (e x) = e (conj x) := by
    intro x
    rw [hφ_apply, e.symm_apply_apply]
  have hez : e ⟨z, hzK⟩ = -1 := by
    have hzsq : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := by
      apply Subtype.ext
      have h := pow_orderOf_eq_one z
      rw [hz2] at h
      simpa [pow_two] using h
    have hsq : e ⟨z, hzK⟩ * e ⟨z, hzK⟩ = 1 := by
      rw [← map_mul, hzsq, map_one]
    rcases sl23_unique_involution _ hsq with h | h
    · exfalso
      have hx1 : (⟨z, hzK⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
      have hz1 : z = 1 := by simpa using congrArg Subtype.val hx1
      rw [hz1] at hz2
      simp at hz2
    · exact h
  rcases sl23_dichotomy φ hφ with hid | ⟨m, hm⟩
  · left
    intro k hk
    have hconjeq : conj ⟨k, hk⟩ = ⟨k, hk⟩ := by
      have h := hid (e ⟨k, hk⟩)
      rw [hφe] at h
      exact e.injective h
    have hval : s * k * s⁻¹ = k := by
      simpa [conj] using congrArg Subtype.val hconjeq
    calc s * k = (s * k * s⁻¹) * s := by group
      _ = k * s := by rw [hval]
  · right
    refine ⟨((e.symm m : ↥K) : G), (e.symm m).2, ?_⟩
    have h_eq : conj (e.symm m) = e.symm m * ⟨z, hzK⟩ := by
      apply e.injective
      have hm' : e (conj (e.symm m)) = m * (-1) := by
        rw [← hφ_apply m]; exact hm
      rw [hm', map_mul, hez, e.apply_symm_apply]
    have hval : s * ((e.symm m : ↥K) : G) * s⁻¹ = ((e.symm m : ↥K) : G) * z := by
      simpa [conj] using congrArg Subtype.val h_eq
    calc ((e.symm m : ↥K) : G)⁻¹ * s * ((e.symm m : ↥K) : G)
        = ((e.symm m : ↥K) : G)⁻¹ * (s * ((e.symm m : ↥K) : G) * s⁻¹) * s := by group
      _ = ((e.symm m : ↥K) : G)⁻¹ * (((e.symm m : ↥K) : G) * z) * s := by rw [hval]
      _ = z * s := by group
      _ = s * z := hsz.symm

end CFSG.OddStandard.SmallF3.Omega