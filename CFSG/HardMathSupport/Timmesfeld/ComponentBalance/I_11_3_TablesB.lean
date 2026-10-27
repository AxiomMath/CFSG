module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

section char2
variable {K : Type*} [Field K] [CharP K 2]

theorem trace_eq_zero_of_pow_two (x : SL(2,K)) (k : ℕ) (hx : x ^ 2 ^ k = 1) :
    x 0 0 + x 1 1 = 0 := by
  induction k generalizing x with
  | zero =>
    have : x = 1 := by simpa using hx
    subst this
    simp only [sl2_one_00, sl2_one_11]
    linear_combination two_eq_zero (K := K)
  | succ k ih =>
    have h := ih (x * x) (by rw [← sq, ← pow_mul, ← pow_succ']; exact hx)
    simp only [sl2_mul_00, sl2_mul_11] at h
    have hdet := sl2_det x
    have : (x 0 0 + x 1 1) ^ 2 = 0 := by
      linear_combination h + 2 * hdet + two_eq_zero (K := K)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this

theorem upper_tri_pow_three [Finite K] (hK : Nat.card K % 3 = 2) (x : SL(2,K)) (hc : x 1 0 = 0)
    (hx3 : x ^ 3 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hdet := sl2_det x
  rw [hc] at hdet
  have hcube : x * x * x = 1 := by rw [← pow_three']; exact hx3
  have e00 := congrArg (fun g : SL(2,K) => g 0 0) hcube
  simp [hc] at e00
  have hp3 : x 0 0 ^ 3 = 1 := by linear_combination e00
  have hp0 : x 0 0 ≠ 0 := by
    intro h; rw [h] at hp3; norm_num at hp3
  have := Fintype.ofFinite K
  have hfp := FiniteField.pow_card_sub_one_eq_one (x 0 0) hp0
  have hcard : Fintype.card K - 1 = 3 * ((Fintype.card K - 1) / 3) + 1 := by
    have : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
    have hpos : 0 < Fintype.card K := Fintype.card_pos
    omega
  have hp1 : x 0 0 = 1 := by
    rw [hcard, pow_succ, pow_mul, hp3, one_pow, one_mul] at hfp
    exact hfp
  have h11 : x 1 1 = 1 := by
    rw [hp1] at hdet; linear_combination hdet
  have e01 := congrArg (fun g : SL(2,K) => g 0 1) hcube
  simp [hc, hp1, h11] at e01
  have hb : x 0 1 = 0 := by linear_combination e01 - (x 0 1) * h2
  apply sl2_ext <;> simp [hc, hp1, h11, hb]

theorem trace_conj_tU_mul_tU (g : SL(2,K)) :
    (g * tU 1 * g⁻¹ * tU 1 : SL(2,K)) 0 0 + (g * tU 1 * g⁻¹ * tU 1 : SL(2,K)) 1 1 = g 1 0 ^ 2 := by
  have hdet := sl2_det g
  simp only [sl2_mul_00, sl2_mul_01, sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_01, sl2_inv_10,
    sl2_inv_11, tU_00, tU_01, tU_10, tU_11]
  linear_combination 2 * hdet + (1 - g 1 0 ^ 2) * two_eq_zero (K := K)

theorem exists_involution_of_isPGroup {G : Type*} [Group G] (S : Subgroup G) (hS : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) : ∃ s ∈ S, s ≠ 1 ∧ s * s = 1 := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS1
  obtain ⟨k, hk⟩ := hS a
  have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact ha (orderOf_eq_one_iff.1 (by simpa using hj))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨((a ^ 2 ^ i : S) : G), (a ^ 2 ^ i).2, ?_, ?_⟩
  · intro h
    have h1 : a ^ 2 ^ i = 1 := Subtype.ext (by simpa using h)
    have := Nat.le_of_dvd (by positivity) (hj ▸ orderOf_dvd_of_pow_eq_one h1)
    have h2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · have : (a ^ 2 ^ i) * (a ^ 2 ^ i) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      rw [← hj]; exact pow_orderOf_eq_one a
    exact congrArg Subtype.val this

theorem eq_one_of_normalizes_two_group [Finite K] (hK : Nat.card K % 3 = 2) (S : Subgroup SL(2,K))
    (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (g : SL(2,K)) (hg3 : g ^ 3 = 1)
    (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g = 1 := by
  obtain ⟨s, hsS, hs1, hss⟩ := exists_involution_of_isPGroup S hS hS1
  obtain ⟨h, hh⟩ := exists_conj_tU_one s hss hs1
  have hus : g * s * g⁻¹ * s ∈ S := S.mul_mem (hgS s hsS) hsS
  obtain ⟨k, hk⟩ := hS ⟨_, hus⟩
  have hk' : (g * s * g⁻¹ * s) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hX : ((h * g * h⁻¹) * tU 1 * (h * g * h⁻¹)⁻¹ * tU 1) ^ 2 ^ k = 1 := by
    have : (h * g * h⁻¹) * tU 1 * (h * g * h⁻¹)⁻¹ * tU 1 = h * (g * s * g⁻¹ * s) * h⁻¹ := by
      rw [← hh]; group
    rw [this, conj_pow, hk']; group
  have htr := trace_eq_zero_of_pow_two _ k hX
  rw [trace_conj_tU_mul_tU] at htr
  have hc : (h * g * h⁻¹) 1 0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp htr
  have hg3' : (h * g * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hg3]; group
  have := upper_tri_pow_three hK _ hc hg3'
  have h2 : g = h⁻¹ * (h * g * h⁻¹) * h := by group
  rw [h2, this]; group

theorem slFieldAut_tU (σ : K ≃+* K) (a : K) : slFieldAut σ (tU a) = tU (σ a) := by
  apply sl2_ext <;> simp [slFieldAut_apply]

theorem cocycle_of_pow_three [Finite K] (g : SL(2,K)) (σ : K ≃+* K)
    (h : (MulAut.conj g * slFieldAut σ) ^ 3 = 1) :
    (∀ x, σ (σ (σ x)) = x) ∧
      g * slFieldAut σ g * slFieldAut σ (slFieldAut σ g) = 1 := by
  set φ := slFieldAut σ with hφ
  set M : SL(2,K) := g * φ g * φ (φ g) with hM
  have hA : ∀ A, M * φ (φ (φ A)) * M⁻¹ = A := by
    intro A
    have := DFunLike.congr_fun h A
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul,
      map_inv, MulAut.one_apply] at this
    refine Eq.trans ?_ this
    rw [hM]; group
  have hφ3 : ∀ a, φ (φ (φ (tU a))) = tU (σ (σ (σ a))) := fun a => by
    simp [hφ, slFieldAut_tU]
  have h1 := hA (tU 1)
  rw [hφ3, map_one, map_one, map_one] at h1
  have hcomm : M * tU 1 = tU 1 * M := by
    rw [mul_inv_eq_iff_eq_mul] at h1; exact h1
  obtain ⟨p, hp⟩ := sl2_comm_tU_one hcomm
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro a
    have := hA (tU a)
    rw [hφ3, hp] at this
    have hc : tU p * tU (σ (σ (σ a))) = tU (σ (σ (σ a))) * tU p := by
      rw [tU_add, tU_add, add_comm]
    rw [hc, mul_assoc, mul_inv_cancel, mul_one] at this
    exact tU_injective this
  refine ⟨hσ3, ?_⟩
  have hφ3' : ∀ A, φ (φ (φ A)) = A := fun A => by
    apply sl2_ext <;> simp [hφ, slFieldAut_apply, hσ3]
  have hmem : M ∈ Subgroup.center SL(2,K) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have := hA A
    rw [hφ3'] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rwa [center_eq_bot, Subgroup.mem_bot] at hmem

theorem indep_two (σ : K ≃+* K) (hσ : ∃ d, σ d ≠ d) (Y Z : K)
    (h : ∀ c, Y * c + Z * σ c = 0) : Y = 0 ∧ Z = 0 := by
  obtain ⟨e, he⟩ := hσ
  have h1 := h 1
  have h2 := h e
  simp only [map_one, mul_one] at h1
  have hZ : Z * (σ e - e) = 0 := by linear_combination h2 - e * h1
  have hZ0 : Z = 0 := (mul_eq_zero.mp hZ).resolve_right (sub_ne_zero.mpr he)
  exact ⟨by rw [hZ0] at h1; simpa using h1, hZ0⟩

theorem indep_three (σ : K ≃+* K) (hσ : ∃ d, σ d ≠ d) (hσ2 : ∃ d, σ (σ d) ≠ d) (x y z : K)
    (h : ∀ c, x * c + y * σ c + z * σ (σ c) = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hYZ : ∀ d, y * (σ d - d) = 0 ∧ z * (σ (σ d) - d) = 0 := by
    intro d
    apply indep_two σ hσ
    intro c
    have h1 := h (σ.symm c * d)
    have h2 := h (σ.symm c)
    simp only [map_mul, RingEquiv.apply_symm_apply] at h1 h2
    linear_combination h1 - d * h2
  obtain ⟨d1, hd1⟩ := hσ
  obtain ⟨d2, hd2⟩ := hσ2
  have hy : y = 0 := (mul_eq_zero.mp (hYZ d1).1).resolve_right (sub_ne_zero.mpr hd1)
  have hz : z = 0 := (mul_eq_zero.mp (hYZ d2).2).resolve_right (sub_ne_zero.mpr hd2)
  have := h 1
  simp only [map_one, mul_one, hy, hz, add_zero] at this
  exact ⟨this, hy, hz⟩

@[expose] def act (g : SL(2,K)) (σ : K ≃+* K) (u : Fin 2 → K) : Fin 2 → K :=
  fun i => g i 0 * σ (u 0) + g i 1 * σ (u 1)

@[expose] def det2 (u v : Fin 2 → K) : K := u 0 * v 1 - u 1 * v 0

theorem act_add (g : SL(2,K)) (σ : K ≃+* K) (u v : Fin 2 → K) :
    act g σ (u + v) = act g σ u + act g σ v := by
  funext i; simp [act, map_add]; ring

theorem act_smul (g : SL(2,K)) (σ : K ≃+* K) (c : K) (u : Fin 2 → K) :
    act g σ (c • u) = σ c • act g σ u := by
  funext i; simp [act, map_mul]; ring

theorem act_cube (g : SL(2,K)) (σ : K ≃+* K) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hN : g * slFieldAut σ g * slFieldAut σ (slFieldAut σ g) = 1) (u : Fin 2 → K) :
    act g σ (act g σ (act g σ u)) = u := by
  have e00 := congrArg (fun A : SL(2,K) => A 0 0) hN
  have e01 := congrArg (fun A : SL(2,K) => A 0 1) hN
  have e10 := congrArg (fun A : SL(2,K) => A 1 0) hN
  have e11 := congrArg (fun A : SL(2,K) => A 1 1) hN
  simp [slFieldAut_apply] at e00 e01 e10 e11
  funext i
  fin_cases i
  · simp [act, map_add, map_mul, hσ3]
    linear_combination u 0 * e00 + u 1 * e01
  · simp [act, map_add, map_mul, hσ3]
    linear_combination u 0 * e10 + u 1 * e11

theorem det2_act (g : SL(2,K)) (σ : K ≃+* K) (u v : Fin 2 → K) :
    det2 (act g σ u) (act g σ v) = σ (det2 u v) := by
  simp only [det2, act, map_sub, map_mul]
  linear_combination (σ (u 0) * σ (v 1) - σ (u 1) * σ (v 0)) * sl2_det g

@[expose] def tvec (g : SL(2,K)) (σ : K ≃+* K) (c : K) (v : Fin 2 → K) : Fin 2 → K :=
  c • v + σ c • act g σ v + σ (σ c) • act g σ (act g σ v)

theorem act_tvec (g : SL(2,K)) (σ : K ≃+* K) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hN : g * slFieldAut σ g * slFieldAut σ (slFieldAut σ g) = 1) (c : K) (v : Fin 2 → K) :
    act g σ (tvec g σ c v) = tvec g σ c v := by
  unfold tvec
  rw [act_add, act_add, act_smul, act_smul, act_smul, act_cube g σ hσ3 hN, hσ3]
  abel

theorem exists_tvec_ne (g : SL(2,K)) (σ : K ≃+* K) (hσ : ∃ d, σ d ≠ d)
    (hσ2 : ∃ d, σ (σ d) ≠ d) (v : Fin 2 → K) (j : Fin 2) (hj : v j ≠ 0) :
    ∃ c, tvec g σ c v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have := indep_three σ hσ hσ2 (v j) (act g σ v j) (act g σ (act g σ v) j) (fun c => by
    have := congrFun (hcon c) j
    simpa [tvec, mul_comm] using this)
  exact hj this.1

theorem det2_act_fixed (g : SL(2,K)) (σ : K ≃+* K) (w : Fin 2 → K) (hw : act g σ w = w)
    (u : Fin 2 → K) : det2 w (act g σ u) = σ (det2 w u) := by
  have := det2_act g σ w u
  rwa [hw] at this

theorem det2_tvec (g : SL(2,K)) (σ : K ≃+* K) (w : Fin 2 → K) (hw : act g σ w = w)
    (c : K) (v : Fin 2 → K) :
    det2 w (tvec g σ c v) =
      c * det2 w v + σ c * σ (det2 w v) + σ (σ c) * σ (σ (det2 w v)) := by
  have h1 := det2_act_fixed g σ w hw v
  have h2 := det2_act_fixed g σ w hw (act g σ v)
  rw [h1] at h2
  have : det2 w (tvec g σ c v) =
      c * det2 w v + σ c * det2 w (act g σ v) + σ (σ c) * det2 w (act g σ (act g σ v)) := by
    simp only [tvec, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, h1, h2]

theorem exists_fixed_pair [Finite K] (g : SL(2,K)) (σ : K ≃+* K) (hσ : ∃ d, σ d ≠ d)
    (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hN : g * slFieldAut σ g * slFieldAut σ (slFieldAut σ g) = 1) :
    ∃ w1 w2 : Fin 2 → K, act g σ w1 = w1 ∧ act g σ w2 = w2 ∧ det2 w1 w2 ≠ 0 := by
  have hσ2 : ∃ d, σ (σ d) ≠ d := by
    by_contra hcon
    push Not at hcon
    obtain ⟨d, hd⟩ := hσ
    apply hd
    have := hσ3 d
    rwa [hcon d] at this
  obtain ⟨c1, hc1⟩ := exists_tvec_ne g σ hσ hσ2 ![1, 0] 0 (by simp)
  set w1 := tvec g σ c1 ![1, 0] with hw1
  have hw1f : act g σ w1 = w1 := act_tvec g σ hσ3 hN _ _
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → K, det2 w1 v ≠ 0 := by
    by_cases h0 : w1 0 = 0
    · have h1 : w1 1 ≠ 0 := by
        intro h1; apply hc1; funext i; fin_cases i <;> simp [h0, h1]
      exact ⟨![1, 0], by simpa [det2, h0] using h1⟩
    · exact ⟨![0, 1], by simpa [det2] using h0⟩
  have hex : ∃ c, det2 w1 (tvec g σ c v) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := indep_three σ hσ hσ2 (det2 w1 v) (σ (det2 w1 v)) (σ (σ (det2 w1 v))) (fun c => by
      have := hcon c
      rw [det2_tvec g σ w1 hw1f] at this
      linear_combination this)
    exact hv this.1
  obtain ⟨c2, hc2⟩ := hex
  exact ⟨w1, tvec g σ c2 v, hw1f, act_tvec g σ hσ3 hN _ _, hc2⟩

theorem exists_fixing_matrix [Finite K] (g : SL(2,K)) (σ : K ≃+* K) (hσ : ∃ d, σ d ≠ d)
    (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hN : g * slFieldAut σ g * slFieldAut σ (slFieldAut σ g) = 1) :
    ∃ P : SL(2,K), g * slFieldAut σ P = P := by
  obtain ⟨w1, w2, hw1, hw2, hd⟩ := exists_fixed_pair g σ hσ hσ3 hN
  set δ := det2 w1 w2 with hδ
  have hσδ : σ δ = δ := by
    have := det2_act_fixed g σ w1 hw1 w2
    rw [hw2] at this
    exact this.symm
  have hw2' : act g σ (δ⁻¹ • w2) = δ⁻¹ • w2 := by
    rw [act_smul, hw2, map_inv₀, hσδ]
  have hdet : w1 0 * (δ⁻¹ • w2) 1 - (δ⁻¹ • w2) 0 * w1 1 = 1 := by
    have : w1 0 * (δ⁻¹ • w2) 1 - (δ⁻¹ • w2) 0 * w1 1 = δ⁻¹ * δ := by
      simp only [hδ, det2, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, inv_mul_cancel₀ hd]
  refine ⟨sl2Mk (w1 0) ((δ⁻¹ • w2) 0) (w1 1) ((δ⁻¹ • w2) 1) hdet, ?_⟩
  have a1 := fun i => congrFun hw1 i
  have a2 := fun i => congrFun hw2' i
  simp only [act, Pi.smul_apply, smul_eq_mul] at a1 a2
  apply sl2_ext
  · simp only [sl2_mul_00, slFieldAut_apply, sl2Mk_00, sl2Mk_10]; exact a1 0
  · simp only [sl2_mul_01, slFieldAut_apply, sl2Mk_01, sl2Mk_11]; exact a2 0
  · simp only [sl2_mul_10, slFieldAut_apply, sl2Mk_00, sl2Mk_10]; exact a1 1
  · simp only [sl2_mul_11, slFieldAut_apply, sl2Mk_01, sl2Mk_11]; exact a2 1

@[expose] def conjUnip (P : SL(2,K)) : Subgroup SL(2,K) where
  carrier := {z | ∃ a, z = P * tU a * P⁻¹}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [← tU_add]; group⟩
  one_mem' := ⟨0, by rw [tU_zero]; group⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [← tU_inv]; group⟩

theorem slFieldAut_wSL (σ : K ≃+* K) : slFieldAut σ (wSL : SL(2,K)) = wSL := by
  apply sl2_ext <;> simp [slFieldAut_apply]

theorem sl2_outer_order_three [Finite K] (β : MulAut SL(2,K)) (h3 : β ^ 3 = 1)
    (hni : ∀ g, β ≠ MulAut.conj g) :
    ∃ y : SL(2,K), orderOf y = 3 ∧ β y = y ∧
      ∃ S : Subgroup SL(2,K), S ≠ ⊥ ∧ IsPGroup 2 S ∧ S.map β.toMonoidHom = S := by
  obtain ⟨g, σ, hβ⟩ := exists_conj_fieldAut β
  have hσ : ∃ d, σ d ≠ d := by
    by_contra hcon
    push Not at hcon
    apply hni g
    have : σ = 1 := RingEquiv.ext hcon
    rw [hβ, this, slFieldAut_one, mul_one]
  rw [hβ] at h3
  obtain ⟨hσ3, hN⟩ := cocycle_of_pow_three g σ h3
  obtain ⟨P, hP⟩ := exists_fixing_matrix g σ hσ hσ3 hN
  have key : ∀ x, β (P * x * P⁻¹) = P * slFieldAut σ x * P⁻¹ := by
    intro x
    rw [hβ]
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv]
    calc g * (slFieldAut σ P * slFieldAut σ x * (slFieldAut σ P)⁻¹) * g⁻¹
        = (g * slFieldAut σ P) * slFieldAut σ x * (g * slFieldAut σ P)⁻¹ := by group
      _ = _ := by rw [hP]
  have hwt : slFieldAut σ (wSL * tU 1 : SL(2,K)) = wSL * tU 1 := by
    rw [map_mul, slFieldAut_wSL, slFieldAut_tU, map_one]
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htU1 : tU (1 : K) ≠ 1 := fun h => by
    have := tU_injective (h.trans tU_zero.symm)
    exact one_ne_zero this
  refine ⟨P * (wSL * tU 1) * P⁻¹, ?_, ?_, conjUnip P, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · have hc : (wSL * tU 1 : SL(2,K)) ^ 3 = 1 := by rw [pow_three']; exact wSL_tU_cube
      rw [conj_pow, hc]; group
    · intro h
      have : (wSL * tU 1 : SL(2,K)) = 1 := by
        have h2 : P⁻¹ * (P * (wSL * tU 1) * P⁻¹) * P = P⁻¹ * 1 * P := by rw [h]
        simpa [mul_assoc] using h2
      have := congrArg (fun g : SL(2,K) => g 0 0) this
      simp at this
  · rw [key, hwt]
  · intro hbot
    have : P * tU 1 * P⁻¹ ∈ conjUnip P := ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    apply htU1
    have h2 : P⁻¹ * (P * tU 1 * P⁻¹) * P = P⁻¹ * 1 * P := by rw [this]
    simpa [mul_assoc] using h2
  · intro z
    obtain ⟨a, ha⟩ := z.2
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : (z : SL(2,K)) ^ 2 ^ 1 = 1 := by
      rw [ha, pow_one, conj_pow, sq, tU_add, CharTwo.add_self_eq_zero, tU_zero]
      group
    simpa using h2
  · ext z
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨σ a, by
        show β (P * tU a * P⁻¹) = _
        rw [key, slFieldAut_tU]⟩
    · rintro ⟨b, rfl⟩
      refine ⟨P * tU (σ.symm b) * P⁻¹, ⟨_, rfl⟩, ?_⟩
      show β (P * tU (σ.symm b) * P⁻¹) = _
      rw [key, slFieldAut_tU, RingEquiv.apply_symm_apply]

end char2

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open scoped MatrixGroups
open SL2Char2 CFSG.Open

theorem two_pow_odd_mod_three {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem IsL2TwoPowOdd.eq_one_of_normalizes {L : Type*} [Group L] (h : IsL2TwoPowOdd L)
    (S : Subgroup L) (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (g : L) (hg3 : g ^ 3 = 1)
    (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g = 1 := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n (by omega)]
    exact two_pow_odd_mod_three hn
  have hS2 : IsPGroup 2 (S.map e.toMonoidHom) := hS.map _
  have hS21 : S.map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply hS1
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hb
    exact hb
  have := eq_one_of_normalizes_two_group hK (S.map e.toMonoidHom) hS2 hS21 (e g)
    (by rw [← map_pow, hg3, map_one]) (by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨g * s * g⁻¹, hgS s hs, by simp⟩)
  exact e.injective (this.trans (map_one e).symm)

theorem table113_T3 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ H S : Subgroup (MulAut L),
    IsElemAbelian 3 H → IsPGroup 2 S → S ≠ ⊥ → H ≤ Subgroup.normalizer (S : Set (MulAut L)) →
      Nat.card H ≤ 3 ∧ H ⊓ innerAut113 L = ⊥ := by
  intro L _ _ h H S hH hS hS1 hHS
  have hinn := h.le_innerAut_of_isPGroup_two S hS
  have hinj := conj_injective_of_center_eq_bot h.center_eq_bot
  have hbot : H ⊓ innerAut113 L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxH, g, rfl⟩
    let S' : Subgroup L := S.comap (MulAut.conj : L →* MulAut L)
    have hS'p : IsPGroup 2 S' := hS.comap_of_injective _ hinj
    have hS'1 : S' ≠ ⊥ := by
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS1
      obtain ⟨b, hb⟩ := hinn a.2
      intro hbot
      have : b ∈ S' := by
        show MulAut.conj b ∈ S
        rw [hb]; exact a.2
      rw [hbot, Subgroup.mem_bot] at this
      apply ha1
      apply Subtype.ext
      rw [← hb, this]; simp
    have hg3 : g ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hH.2 _ hxH)
    have hg1 : g = 1 := h.eq_one_of_normalizes S' hS'p hS'1 g hg3 (fun s hs => by
      have := (Subgroup.mem_normalizer_iff.1 (hHS hxH) (MulAut.conj s)).1 hs
      show MulAut.conj (g * s * g⁻¹) ∈ S
      simpa using this)
    rw [hg1, map_one]
  refine ⟨?_, hbot⟩
  have hcyc := h.outer_isCyclic
  let f : H →* MulAut L ⧸ innerAut113 L := (QuotientGroup.mk' (innerAut113 L)).comp H.subtype
  have hker : Nat.card f.ker = 1 := by
    have : f.ker = (H ⊓ innerAut113 L).subgroupOf H := by
      ext x
      simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    rw [this, hbot]
    simp
  have hrange : Nat.card f.range ≤ 3 := by
    refine card_le_three_of_cyclic fun x => ?_
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [← hy]
    change f (y ^ 3) = 1
    have : y ^ 3 = 1 := Subtype.ext (hH.2 y y.2)
    rw [this, map_one]
  rw [← Subgroup.card_ker_mul_card_range f, hker, one_mul]
  exact hrange

theorem table113_T4 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ α : MulAut L,
    orderOf α = 3 → α ∉ innerAut113 L → (∃ y : L, orderOf y = 3 ∧ α y = y) ∧
      ∃ S : Subgroup L, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S.map α.toMonoidHom = S := by
  intro L _ _ h α hα3 hαni
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  let β : MulAut SL(2, GaloisField 2 n) := MulAut.congr e α
  have hβ3 : β ^ 3 = 1 := by
    have : β ^ 3 = MulAut.congr e (α ^ 3) := (map_pow _ _ _).symm
    rw [this, ← hα3, pow_orderOf_eq_one, map_one]
  have hβni : ∀ g, β ≠ MulAut.conj g := by
    intro g hg
    apply hαni
    have : α = (MulAut.congr e).symm β := ((MulAut.congr e).symm_apply_apply α).symm
    rw [this, hg, congr_symm_conj]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy3, hyf, S, hS1, hSp, hSm⟩ := sl2_outer_order_three β hβ3 hβni
  refine ⟨⟨e.symm y, ?_, ?_⟩, S.map e.symm.toMonoidHom, ?_, hSp.map _, ?_⟩
  · exact (MulEquiv.orderOf_eq e.symm y).trans hy3
  · apply e.injective
    have : e (α (e.symm y)) = y := hyf
    rw [this]; simp
  · intro hb
    apply hS1
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at hb
    exact hb
  · rw [Subgroup.map_map]
    have : α.toMonoidHom.comp e.symm.toMonoidHom = e.symm.toMonoidHom.comp β.toMonoidHom := by
      ext x; simp [β, MulAut.congr_apply]
    rw [this, ← Subgroup.map_map, hSm]

theorem tables113 : Tables113 := ⟨table113_T0, table113_T2, table113_T3, table113_T4⟩

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
