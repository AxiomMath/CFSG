module

public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerSL2
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.ABGLocalTools

open Matrix CFSG.QuasiDihedralFusion

universe u

section Basic

variable {F : Type u} [Field F] [Finite F]

theorem ringChar_prime : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)

theorem ringChar_ne_two_of_odd_card (hodd : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F (ringChar F)
  intro h2
  rw [Nat.card_eq_fintype_card, hq, h2] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' n.ne_zero).mpr even_two)

theorem card_eq_ringChar_pow : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = ringChar F ^ f := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F (ringChar F)
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hq]⟩

omit [Finite F] in
theorem sl2U_mul_sl2U_sq :
    (sl2U * sl2U : SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_sl2U_mul_sl2U]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [Finite F] in
theorem sq_eq_one_of_mem_center {c : SpecialLinearGroup (Fin 2) F}
    (hc : c ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : c ^ 2 = 1 := by
  rcases sl2_mem_center_iff.mp hc with rfl | rfl
  · exact one_pow 2
  · exact sl2U_mul_sl2U_sq

end Basic

section Inner

variable {F : Type u} [Field F] [Finite F]

theorem eq_conj_of_inv_mul_conj_mem_center (hF : ringChar F ≠ 2)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (j : SpecialLinearGroup (Fin 2) F)
    (h : ∀ b, (α b)⁻¹ * (j * b * j⁻¹) ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    α = MulAut.conj j := by
  have hr : (ringChar F).Prime := ringChar_prime
  have key : α.toMonoidHom = (MulAut.conj j).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense
      SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    rintro _ ⟨t, rfl⟩
    set x := t.toSpecialLinearGroup with hx
    have hxr : x ^ ringChar F = 1 := CFSG.LieType.CentralExt.toSpecialLinearGroup_pow_ringChar t
    set c := (α x)⁻¹ * (j * x * j⁻¹) with hcdef
    have hc := h x
    rw [← hcdef] at hc
    have hjx : j * x * j⁻¹ = α x * c := by rw [hcdef, mul_inv_cancel_left]
    have hcomm : Commute (α x) c := Subgroup.mem_center_iff.mp hc (α x)
    have hcr : c ^ ringChar F = 1 := by
      have h1 : (j * x * j⁻¹) ^ ringChar F = 1 := by rw [conj_pow, hxr, mul_one, mul_inv_cancel]
      rw [hjx, hcomm.mul_pow, ← map_pow, hxr, map_one, one_mul] at h1
      exact h1
    have hc2 : c ^ 2 = 1 := sq_eq_one_of_mem_center hc
    have hc1 : c = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hcr
      have h2 := orderOf_dvd_of_pow_eq_one hc2
      have hcop : Nat.Coprime (ringChar F) 2 :=
        (Nat.coprime_primes hr Nat.prime_two).mpr hF
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [hc1, mul_one] at hjx
    change α x = j * x * j⁻¹
    exact hjx.symm
  exact MulEquiv.ext (fun b => DFunLike.congr_fun key b)

end Inner

section CardThree

variable {F : Type u} [Field F] [Finite F]

theorem ringChar_eq_three_of_card (h3 : Nat.card F = 3) : ringChar F = 3 := by
  obtain ⟨f, hf, hq⟩ := card_eq_ringChar_pow (F := F)
  have hr := ringChar_prime (F := F)
  have hdvd : ringChar F ∣ 3 := by
    rw [← h3, hq]
    exact dvd_pow_self _ (by omega)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hr.one_lt.ne'
  · exact h

theorem mulAut_eq_one_of_card_three (h3 : Nat.card F = 3) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα : α ^ p = 1) : α = 1 := by
  classical
  have hpp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) F) = 24 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, h3]
    norm_num
  have hU3 : ∀ U : Sylow 3 (SpecialLinearGroup (Fin 2) F), Nat.card U = 3 := by
    intro U
    obtain ⟨k, hk⟩ := U.isPGroup'.exists_card_eq
    have hdvd : 3 ^ k ∣ 24 := by
      rw [← hk, ← hcard]
      exact Subgroup.card_subgroup_dvd_card (U : Subgroup (SpecialLinearGroup (Fin 2) F))
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h9
    have hidx := (U : Subgroup (SpecialLinearGroup (Fin 2) F)).card_mul_index
    rw [hcard] at hidx
    have hnd := U.not_dvd_index
    interval_cases k
    · exfalso
      rw [show Nat.card (U : Subgroup (SpecialLinearGroup (Fin 2) F)) = 1 by
        rw [hk, pow_zero], one_mul] at hidx
      exact hnd (by rw [hidx]; norm_num)
    · rw [hk, pow_one]
  have hsyl : Nat.card (Sylow 3 (SpecialLinearGroup (Fin 2) F)) ≤ 4 := by
    obtain ⟨U⟩ : Nonempty (Sylow 3 (SpecialLinearGroup (Fin 2) F)) := inferInstance
    have hdvd := Sylow.card_dvd_index U
    have hidx : (U : Subgroup (SpecialLinearGroup (Fin 2) F)).index = 8 := by
      have h := (U : Subgroup (SpecialLinearGroup (Fin 2) F)).card_mul_index
      rw [hcard, hU3 U] at h
      omega
    rw [hidx] at hdvd
    have hmod := card_sylow_modEq_one 3 (SpecialLinearGroup (Fin 2) F)
    have hpos : 0 < Nat.card (Sylow 3 (SpecialLinearGroup (Fin 2) F)) := Nat.card_pos
    have hle : Nat.card (Sylow 3 (SpecialLinearGroup (Fin 2) F)) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hdvd
    set n := Nat.card (Sylow 3 (SpecialLinearGroup (Fin 2) F))
    unfold Nat.ModEq at hmod
    interval_cases n <;> omega
  have hfix : ∀ U : Sylow 3 (SpecialLinearGroup (Fin 2) F), α • U = U := by
    let π := MulAction.toPermHom (MulAut (SpecialLinearGroup (Fin 2) F))
      (Sylow 3 (SpecialLinearGroup (Fin 2) F)) α
    have hπp : π ^ p = 1 := by
      rw [← map_pow, hα, map_one]
    have hord : orderOf π ∣ p := orderOf_dvd_of_pow_eq_one hπp
    have hord2 : orderOf π ∣ 24 := by
      have h1 : orderOf π ∣ Nat.card (Equiv.Perm (Sylow 3 (SpecialLinearGroup (Fin 2) F))) :=
        orderOf_dvd_natCard π
      rw [Nat.card_perm] at h1
      exact h1.trans ((Nat.factorial_dvd_factorial hsyl).trans (by decide))
    have hπ1 : π = 1 := by
      rcases (Nat.dvd_prime hpp).mp hord with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        rw [h] at hord2
        have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
        rw [h24] at hord2
        rcases (Nat.Prime.dvd_mul hpp).mp hord2 with h2 | h3'
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h2))
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3')
    intro U
    have h := congrArg (fun π : Equiv.Perm (Sylow 3 (SpecialLinearGroup (Fin 2) F)) => π U) hπ1
    simpa [π] using h
  have hfixU : ∀ U : Sylow 3 (SpecialLinearGroup (Fin 2) F), ∀ x ∈ (U : Subgroup _),
      α x = x := by
    intro U x hx
    have hαU : α x ∈ (U : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
      have h : α x ∈ ((α • U : Sylow 3 _) : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
        rw [Sylow.pointwise_smul_def]
        exact Subgroup.smul_mem_pointwise_smul x α _ hx
      rwa [hfix U] at h
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    have hox : orderOf x = 3 := by
      have h1 : orderOf x ∣ 3 := by
        have h := orderOf_dvd_natCard (⟨x, hx⟩ : (U : Subgroup (SpecialLinearGroup (Fin 2) F)))
        rwa [Subgroup.orderOf_mk, hU3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hzU : Subgroup.zpowers x = (U : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      rw [Nat.card_zpowers, hox, hU3]
    rw [← hzU, mem_zpowers_iff_mem_range_orderOf, hox] at hαU
    obtain ⟨k, hk, hxk⟩ := Finset.mem_image.mp hαU
    have hk3 : k < 3 := Finset.mem_range.mp hk
    have hx3 : x ^ 3 = 1 := by rw [← hox]; exact pow_orderOf_eq_one x
    interval_cases k
    · exfalso
      apply hx1
      apply α.injective
      rw [← hxk, pow_zero, map_one]
    · rw [← hxk, pow_one]
    · exfalso
      have h2 : (α ^ 2) x = x := by
        rw [pow_two, MulAut.mul_apply, ← hxk, map_pow, ← hxk, ← pow_mul,
          show x ^ (2 * 2) = x ^ 3 * x by group, hx3, one_mul]
      have h2m : ∀ m : ℕ, (α ^ (2 * m)) x = x := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [Nat.mul_succ, pow_add, MulAut.mul_apply, h2, ih]
      obtain ⟨m, hm⟩ := hpp.odd_of_ne_two hp2
      have hpx : (α ^ p) x = x := by rw [hα, MulAut.one_apply]
      rw [hm, pow_succ, MulAut.mul_apply, ← hxk, map_pow, h2m] at hpx
      apply hx1
      have h' : x * x = x * 1 := by rw [mul_one, ← pow_two, hpx]
      exact mul_left_cancel h'
  have key : α.toMonoidHom = (1 : MulAut (SpecialLinearGroup (Fin 2) F)).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense
      SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    rintro _ ⟨t, rfl⟩
    set x := t.toSpecialLinearGroup with hxdef
    have hx3 : x ^ 3 = 1 := by
      rw [← ringChar_eq_three_of_card h3]
      exact CFSG.LieType.CentralExt.toSpecialLinearGroup_pow_ringChar t
    have hz : IsPGroup 3 (Subgroup.zpowers x) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show orderOf x ∣ 3 ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hx3)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨U, hU⟩ := hz.exists_le_sylow
    exact hfixU U x (hU (Subgroup.mem_zpowers x))
  exact MulEquiv.ext (fun b => DFunLike.congr_fun key b)

end CardThree

end CFSG.ABGLocalTools
