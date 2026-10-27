module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatThree

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

@[expose] def b3 : Perm (Fin 11) := swap 10 0 * swap 0 1

@[expose] def piB : Perm (Fin 11) := swap 8 10 * swap 10 1 * swap 1 9 * swap 9 0

@[expose] def v1 : Perm (Fin 11) := swap 0 9 * swap 8 10

@[expose] def v2 : Perm (Fin 11) := swap 0 8 * swap 9 10

theorem v1_sq : v1 * v1 = 1 := by decide

theorem v2_sq : v2 * v2 = 1 := by decide

theorem v12_comm : v1 * v2 = v2 * v1 := by decide

variable {K : Type} [Group K]

theorem mem_of_dbl (C : CoverSetup 11 K) {Y : Subgroup K} {n : K} (hn : n ∈ Y)
    (hd : DblI (C.ρ n)) : ∀ c ∈ center K, c ∈ Y := fun c hc => by
  by_cases h1 : c = 1
  · rw [h1]
    exact one_mem _
  · rw [Cov.center_eq C hc (C.sq_mem_center hd.1) h1 (C.dblI_sq_ne_one (by norm_num) hd)]
    exact mul_mem hn hn

theorem sl25_of_t3 [Finite K] (C : CoverSetup 11 K) {a : K} (ha : C.ρ a = t3) (ha3 : a ^ 3 = 1) :
    ∃ h : K, closure {y : K | y ∈ closure ({a, h * a * h⁻¹} : Set K) ∧ orderOf y = 5} =
        closure ({a, h * a * h⁻¹} : Set K) ∧
      8 ∣ Nat.card ↥(closure ({a, h * a * h⁻¹} : Set K)) := by
  obtain ⟨h, hh⟩ := C.exists_ρ_eq (show sign piB = 1 by decide)
  refine ⟨h, ?_⟩
  obtain ⟨b, hbdef⟩ : ∃ b, h * a * h⁻¹ = b := ⟨_, rfl⟩
  rw [hbdef]
  have hb : C.ρ b = b3 := by
    rw [← hbdef, map_mul, map_mul, map_inv, hh, ha]
    decide
  generalize hY : closure ({a, b} : Set K) = Y
  have haY : a ∈ Y := by rw [← hY]; exact subset_closure (Set.mem_insert _ _)
  have hbY : b ∈ Y := by rw [← hY]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hwY : a * b * a * b⁻¹ ∈ Y := mul_mem (mul_mem (mul_mem haY hbY) haY) (inv_mem hbY)
  have hwρ : C.ρ (a * b * a * b⁻¹) = v1 := by
    rw [map_mul, map_mul, map_mul, map_inv, ha, hb]
    decide
  have hw'Y : a⁻¹ * b * a⁻¹ * b⁻¹ ∈ Y :=
    mul_mem (mul_mem (mul_mem (inv_mem haY) hbY) (inv_mem haY)) (inv_mem hbY)
  have hw'ρ : C.ρ (a⁻¹ * b * a⁻¹ * b⁻¹) = v2 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]
    decide
  have hZY := mem_of_dbl C hwY (by rw [hwρ]; unfold DblI; decide)
  refine ⟨le_antisymm (closure_le _ |>.2 fun y hy => hy.1) ?_, ?_⟩
  · set Y5 := closure {y : K | y ∈ Y ∧ orderOf y = 5} with hY5
    have h5 : ∀ m ∈ Y, C.ρ m ^ 5 = 1 → C.ρ m ≠ 1 → ∃ c ∈ center K, m * c ∈ Y5 := by
      intro m hm h5 h1
      obtain ⟨c, hc, hmc⟩ := Cov.exists_lift_prime C (by norm_num) (by norm_num) h5 h1
      exact ⟨c, hc, subset_closure ⟨mul_mem hm (hZY c hc), hmc⟩⟩
    obtain ⟨c1, hc1, h1⟩ := h5 (a * b) (mul_mem haY hbY)
      (by rw [map_mul, ha, hb]; decide) (by rw [map_mul, ha, hb]; decide)
    obtain ⟨c2, hc2, h2⟩ := h5 (a⁻¹ * b) (mul_mem (inv_mem haY) hbY)
      (by rw [map_mul, map_inv, ha, hb]; decide) (by rw [map_mul, map_inv, ha, hb]; decide)
    obtain ⟨c3, hc3, h3⟩ := h5 (a * b⁻¹) (mul_mem haY (inv_mem hbY))
      (by rw [map_mul, map_inv, ha, hb]; decide) (by rw [map_mul, map_inv, ha, hb]; decide)
    have hZY5 := mem_of_dbl C (mul_mem h1 h3) (by
      simp only [map_mul, map_inv]
      rw [ha, hb, (C.ρ_eq_one_iff).2 hc1, (C.ρ_eq_one_iff).2 hc3]
      unfold DblI
      decide)
    have hm1 : a * b ∈ Y5 := by
      have := mul_mem h1 (hZY5 _ (inv_mem hc1))
      rwa [mul_inv_cancel_right] at this
    have hm2 : a⁻¹ * b ∈ Y5 := by
      have := mul_mem h2 (hZY5 _ (inv_mem hc2))
      rwa [mul_inv_cancel_right] at this
    have haY5 : a ∈ Y5 := by
      have e2 : (a * b) * (a⁻¹ * b)⁻¹ = a * a := by group
      have e : a = ((a * b) * (a⁻¹ * b)⁻¹) * ((a * b) * (a⁻¹ * b)⁻¹) := by
        rw [e2]
        calc a = a ^ 3 * a := by rw [ha3, one_mul]
          _ = (a * a) * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e]
      exact mul_mem (mul_mem hm1 (inv_mem hm2)) (mul_mem hm1 (inv_mem hm2))
    have hbY5 : b ∈ Y5 := by
      have e : b = a⁻¹ * (a * b) := by group
      rw [e]
      exact mul_mem (inv_mem haY5) hm1
    rw [← hY, closure_le]
    rintro y (rfl | rfl)
    · exact haY5
    · exact hbY5
  · have hVA : kleinSub v1 v2 v1_sq v2_sq v12_comm ≤ alternatingGroup (Fin 11) := by
      rintro x (rfl | rfl | rfl | rfl) <;> rw [Perm.mem_alternatingGroup] <;> decide
    have hT : Nat.card ((kleinSub v1 v2 v1_sq v2_sq v12_comm).comap C.ρ) = 8 := by
      rw [C.card_comap hVA, card_kleinSub v1_sq v2_sq v12_comm (by decide) (by decide)
        (by decide)]
    rw [← hT]
    refine Subgroup.card_dvd_of_le fun t ht => ?_
    have key : ∀ w ∈ Y, C.ρ t = C.ρ w → t ∈ Y := fun w hw hρ => by
      have hc : w⁻¹ * t ∈ center K := by
        rw [← C.ρ_eq_one_iff, map_mul, map_inv, hρ, inv_mul_cancel]
      have := mul_mem hw (hZY _ hc)
      rwa [mul_inv_cancel_left] at this
    rcases (show C.ρ t ∈ kleinSub v1 v2 v1_sq v2_sq v12_comm from ht) with h | h | h | h
    · exact hZY t ((C.ρ_eq_one_iff).1 h)
    · exact key _ hwY (h.trans hwρ.symm)
    · exact key _ hw'Y (h.trans hw'ρ.symm)
    · exact key _ (mul_mem hwY hw'Y) (by rw [h, map_mul, hwρ, hw'ρ])

theorem specB4 : SpecB4 := by
  intro K _ _ S hK hS hc x hx3 hxS
  obtain ⟨C, x₀, hSP, hx₀, h3⟩ := exists_std hK hS hc
  have hx0' : x₀ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one x₀
  have hxx : x ∈ zpowers x₀ := le_zpowers_x0 C hSP hx₀ h3
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])) hxS (mem_zpowers x)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hxx
  rw [← zpow_mod_orderOf, h3] at hj
  have hj3 : j % ((3 : ℕ) : ℤ) = 0 ∨ j % ((3 : ℕ) : ℤ) = 1 ∨ j % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hj3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hj
    rw [← hj, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  · rw [h1, zpow_one] at hj
    subst hj
    exact sl25_of_t3 C hx₀ hx0'
  · rw [h2] at hj
    have hxinv : x = x₀⁻¹ := by
      rw [← hj, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, hx0']
    subst hxinv
    obtain ⟨h, h1', h2'⟩ := sl25_of_t3 C hx₀ hx0'
    refine ⟨h, ?_⟩
    have e : ({x₀⁻¹, h * x₀⁻¹ * h⁻¹} : Set K) = ({x₀, h * x₀ * h⁻¹} : Set K)⁻¹ := by
      rw [Set.inv_insert, Set.inv_singleton, show (h * x₀ * h⁻¹)⁻¹ = h * x₀⁻¹ * h⁻¹ by group]
    rw [e, Subgroup.closure_inv]
    exact ⟨h1', h2'⟩

end CFSG.OddStandard.GH71.AhatB
