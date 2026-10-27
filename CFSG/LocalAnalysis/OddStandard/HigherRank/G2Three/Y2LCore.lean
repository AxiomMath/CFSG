module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPres
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LCodes
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LRho

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix

@[expose] def y2l_S0 : List ℕ := [0, 1, 0, 0, 0, 1, 1, 3, 1]

@[expose] def y2l_RS : List ℕ := [3, 1, 3, 0, 0, 3, 0, 3, 0]

@[expose] def y2l_wcode : List Bool → List ℕ
  | [] => y2l_one3
  | l :: w => y2l_mul3 (bif l then y2l_beta0 else y2l_alpha0) (y2l_wcode w)

@[expose] def y2l_wprod {X : Type} [Group X] (a b : X) : List Bool → X
  | [] => 1
  | l :: w => (bif l then b else a) * y2l_wprod a b w

@[expose] def y2l_ws0 : List Bool := [false, true, false, true, true]

@[expose] def y2l_w1 : List Bool :=
  [true, true, false, true, true, false, true, false, true, false, true]

@[expose] def y2l_w2 : List Bool := [true, true, false, true, true, false, true, false, true, false]

theorem y2l_wcode_ws0 : y2l_wcode y2l_ws0 = y2l_S0 := by decide

theorem y2l_pow3_S0_four : y2l_pow3 y2l_S0 4 = y2l_one3 := by decide

theorem y2l_fus1 :
    y2l_mul3 (y2l_pow3 y2l_S0 2) (y2l_wcode y2l_w1) = y2l_mul3 (y2l_wcode y2l_w1) y2l_alpha0 := by
  decide

theorem y2l_fus2 :
    y2l_mul3 (y2l_pow3 y2l_S0 2) (y2l_wcode y2l_w2) = y2l_mul3 (y2l_wcode y2l_w2) y2l_RS := by
  decide

theorem y2l_mul3_RS : y2l_mul3 y2l_alpha0 y2l_RS = y2l_S0 := by decide

theorem y2l_fix_S0 :
    ∀ a b c : ZMod 4, ![a, b, c] ᵥ* y2l_dec y2l_S0 = ![a, b, c] → b = 0 ∧ c = a := by
  decide

theorem y2l_j_vec : ∀ k : ZMod 4,
    ![k, 0, k] + ![-k, 0, 0] ᵥ* y2l_dec (y2l_pow3 y2l_S0 2) + ![-k, 0, 0] = 0 := by
  decide

theorem y2l_norm_vec : (![0, 0, 3] : Fin 3 → ZMod 4) ᵥ* y2l_dec (y2l_pow3 y2l_S0 3) +
    ![0, 0, 3] ᵥ* y2l_dec (y2l_pow3 y2l_S0 2) + ![0, 0, 3] ᵥ* y2l_dec y2l_S0 + ![0, 0, 3] =
      ![2, 0, 2] := by
  decide

theorem y2l_vec_v : (![0, 1, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_alpha0 + ![0, 1, 0] = 0 := by
  decide

theorem y2l_vec_RS : (![0, 1, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_RS = ![0, 0, 3] := by decide

theorem y2l_row_R0 : (![1, 0, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_alpha0 = -![0, 0, 1] := by
  decide

theorem y2l_row_R1 : (![0, 1, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_alpha0 = -![0, 1, 0] := by
  decide

theorem y2l_row_R2 : (![0, 0, 1] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_alpha0 = -![1, 0, 0] := by
  decide

theorem y2l_row_S0 : (![1, 0, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_S0 = ![0, 1, 0] := by decide

theorem y2l_row_S1 : (![0, 1, 0] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_S0 = ![0, 0, 1] := by decide

theorem y2l_row_S2 :
    (![0, 0, 1] : Fin 3 → ZMod 4) ᵥ* y2l_dec y2l_S0 = ![1, 0, 0] + -![0, 1, 0] + ![0, 0, 1] := by
  decide

theorem y2l_add_202 : ∀ k : ZMod 4, ![k, 0, k] + ![2, 0, 2] = ![k + 2, 0, k + 2] := by decide

theorem y2l_zmod4_cases : ∀ k : ZMod 4, (k = 0 ∨ k = 1) ∨ (k + 2 = 0 ∨ k + 2 = 1) := by decide

theorem y2l_four_nsmul (c : Fin 3 → ZMod 4) : (4 : ℕ) • c = 0 := by
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem y2l_vec_eta (c : Fin 3 → ZMod 4) : ![c 0, c 1, c 2] = c := by
  funext i
  fin_cases i <;> rfl

variable {X : Type} [Group X] {M : Subgroup X} [M.Normal]
  (τ : M ≃* Multiplicative (Fin 3 → ZMod 4))

theorem y2l_rho_wprod {a b : X} (ha : y2l_rho τ a = y2l_dec y2l_alpha0)
    (hb : y2l_rho τ b = y2l_dec y2l_beta0) :
    ∀ w : List Bool, y2l_rho τ (y2l_wprod a b w) = y2l_dec (y2l_wcode w)
  | [] => by rw [y2l_wprod, y2l_wcode, map_one, y2l_dec_one3]
  | l :: w => by
    rw [y2l_wprod, y2l_wcode, map_mul, y2l_rho_wprod ha hb w, y2l_dec_mul3]
    cases l <;> simp only [cond_false, cond_true, ha, hb]

theorem y2l_rho_conj {y j : X} {N : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (h : y2l_rho τ j * y2l_rho τ y = y2l_rho τ y * N) : y2l_rho τ (y⁻¹ * j * y) = N := by
  rw [map_mul, map_mul, mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem y2l_conj_sq {y j : X} (h : j * j = 1) : y⁻¹ * j * y * (y⁻¹ * j * y) = 1 := by
  calc y⁻¹ * j * y * (y⁻¹ * j * y) = y⁻¹ * (j * j) * y := by group
    _ = 1 := by rw [h, mul_one, inv_mul_cancel]

theorem y2l_pow4_of_rho (hC : centralizer (M : Set X) = M) {s : X}
    (hs : y2l_rho τ s = y2l_dec y2l_S0) : ∃ k : ZMod 4, s ^ 4 = y2l_el τ ![k, 0, k] := by
  have hM : s ^ 4 ∈ M := by
    rw [← y2l_rho_eq_one_iff τ hC, map_pow, hs, ← y2l_dec_pow3, y2l_pow3_S0_four, y2l_dec_one3]
  obtain ⟨c, hc⟩ := y2l_exists_el τ hM
  have hfix : ![c 0, c 1, c 2] ᵥ* y2l_dec y2l_S0 = ![c 0, c 1, c 2] := by
    rw [y2l_vec_eta]
    apply y2l_el_injective τ
    rw [← hs, ← y2l_conj_el, hc]
    group
  obtain ⟨h1, h2⟩ := y2l_fix_S0 _ _ _ hfix
  refine ⟨c 0, ?_⟩
  rw [← hc]
  congr 1
  funext i
  fin_cases i <;> simp [h1, h2]

theorem y2l_exists_j (hC : centralizer (M : Set X) = M) {s₀ : X}
    (hs : y2l_rho τ s₀ = y2l_dec y2l_S0) :
    ∃ j : X, y2l_rho τ j = y2l_dec (y2l_pow3 y2l_S0 2) ∧ j * j = 1 := by
  obtain ⟨k, hk⟩ := y2l_pow4_of_rho τ hC hs
  refine ⟨s₀ ^ 2 * y2l_el τ ![-k, 0, 0], ?_, ?_⟩
  · rw [map_mul, map_pow, hs, y2l_rho_of_mem τ (y2l_el_mem τ _), mul_one, y2l_dec_pow3]
  · calc s₀ ^ 2 * y2l_el τ ![-k, 0, 0] * (s₀ ^ 2 * y2l_el τ ![-k, 0, 0]) =
          s₀ ^ 4 * ((s₀ ^ 2)⁻¹ * y2l_el τ ![-k, 0, 0] * s₀ ^ 2) * y2l_el τ ![-k, 0, 0] := by
          group
      _ = 1 := by
        rw [hk, y2l_conj_el, map_pow, hs, ← y2l_dec_pow3, ← y2l_el_add, ← y2l_el_add, y2l_j_vec,
          y2l_el_zero]

theorem y2l_exists_frame (hC : centralizer (M : Set X) = M) {xa xb : X}
    (ha : y2l_rho τ xa = y2l_dec y2l_alpha0) (hb : y2l_rho τ xb = y2l_dec y2l_beta0) :
    ∃ r t : X, y2l_rho τ r = y2l_dec y2l_alpha0 ∧ y2l_rho τ t = y2l_dec y2l_RS ∧ r * r = 1 ∧
      t * t = 1 := by
  obtain ⟨j, hj, hj2⟩ := y2l_exists_j τ hC (s₀ := y2l_wprod xa xb y2l_ws0)
    (by rw [y2l_rho_wprod τ ha hb, y2l_wcode_ws0])
  have hW : ∀ (w : List Bool) (N : List ℕ),
      y2l_mul3 (y2l_pow3 y2l_S0 2) (y2l_wcode w) = y2l_mul3 (y2l_wcode w) N →
      y2l_rho τ ((y2l_wprod xa xb w)⁻¹ * j * y2l_wprod xa xb w) = y2l_dec N := fun w N h =>
    y2l_rho_conj τ (by rw [hj, y2l_rho_wprod τ ha hb, ← y2l_dec_mul3, h, y2l_dec_mul3])
  exact ⟨_, _, hW _ _ y2l_fus1, hW _ _ y2l_fus2, y2l_conj_sq hj2, y2l_conj_sq hj2⟩

theorem y2l_pow4_mul_el {s : X} (hs : y2l_rho τ s = y2l_dec y2l_S0) (c : Fin 3 → ZMod 4) :
    (s * y2l_el τ c) ^ 4 = s ^ 4 * y2l_el τ (c ᵥ* y2l_dec (y2l_pow3 y2l_S0 3) +
      c ᵥ* y2l_dec (y2l_pow3 y2l_S0 2) + c ᵥ* y2l_dec y2l_S0 + c) := by
  have hρ : ∀ i : ℕ, y2l_rho τ (s ^ i) = y2l_dec (y2l_pow3 y2l_S0 i) := fun i => by
    rw [map_pow, hs, y2l_dec_pow3]
  have h4 : ∀ y : X, y ^ 4 = y * y * y * y := fun y => by
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]
  calc (s * y2l_el τ c) ^ 4 = s * y2l_el τ c * (s * y2l_el τ c) * (s * y2l_el τ c) *
        (s * y2l_el τ c) := h4 _
    _ = s ^ 4 * ((s ^ 3)⁻¹ * y2l_el τ c * s ^ 3) * ((s ^ 2)⁻¹ * y2l_el τ c * s ^ 2) *
        (s⁻¹ * y2l_el τ c * s) * y2l_el τ c := by group
    _ = _ := by
      rw [y2l_conj_el, y2l_conj_el, y2l_conj_el, hρ, hρ, hs]
      simp only [y2l_el_add, mul_assoc]

theorem y2l_rels_of_frame {r t : X} (hr : y2l_rho τ r = y2l_dec y2l_alpha0)
    (ht : y2l_rho τ t = y2l_dec y2l_RS) (hr2 : r * r = 1) (ht2 : t * t = 1) {e : Bool}
    (hs4 : (r * t) ^ 4 = if e then y2l_el τ ![1, 0, 0] * y2l_el τ ![0, 0, 1] else 1) :
    Y2LRels 2 e (y2l_el τ ![1, 0, 0]) (y2l_el τ ![0, 1, 0]) (y2l_el τ ![0, 0, 1]) r (r * t) := by
  have hs : y2l_rho τ (r * t) = y2l_dec y2l_S0 := by
    rw [map_mul, hr, ht, ← y2l_dec_mul3, y2l_mul3_RS]
  have hp : ∀ c : Fin 3 → ZMod 4, y2l_el τ c ^ 2 ^ 2 = 1 := fun c => by
    rw [← y2l_el_nsmul, show (2 : ℕ) ^ 2 = 4 by norm_num, y2l_four_nsmul, y2l_el_zero]
  refine ⟨y2l_comm τ (y2l_el_mem τ _) (y2l_el_mem τ _), y2l_comm τ (y2l_el_mem τ _)
    (y2l_el_mem τ _), y2l_comm τ (y2l_el_mem τ _) (y2l_el_mem τ _), hp _, hp _, hp _,
    by rw [pow_two, hr2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs4⟩
  · rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hr2,
      ← mul_assoc, hr2, one_mul]
  · rw [y2l_conj_el, hr, y2l_row_R0, y2l_el_neg]
  · rw [y2l_conj_el, hr, y2l_row_R1, y2l_el_neg]
  · rw [y2l_conj_el, hr, y2l_row_R2, y2l_el_neg]
  · rw [y2l_conj_el, hs, y2l_row_S0]
  · rw [y2l_conj_el, hs, y2l_row_S1]
  · rw [y2l_conj_el, hs, y2l_row_S2, y2l_el_add, y2l_el_add, y2l_el_neg]

theorem y2l_adjust {r t : X} (hr : y2l_rho τ r = y2l_dec y2l_alpha0)
    (ht : y2l_rho τ t = y2l_dec y2l_RS) (hr2 : r * r = 1) :
    y2l_rho τ (r * y2l_el τ ![0, 1, 0]) = y2l_dec y2l_alpha0 ∧
      r * y2l_el τ ![0, 1, 0] * (r * y2l_el τ ![0, 1, 0]) = 1 ∧
      (r * y2l_el τ ![0, 1, 0] * t) ^ 4 = (r * t) ^ 4 * y2l_el τ ![2, 0, 2] := by
  have hs : y2l_rho τ (r * t) = y2l_dec y2l_S0 := by
    rw [map_mul, hr, ht, ← y2l_dec_mul3, y2l_mul3_RS]
  refine ⟨by rw [map_mul, hr, y2l_rho_of_mem τ (y2l_el_mem τ _), mul_one], ?_, ?_⟩
  · calc r * y2l_el τ ![0, 1, 0] * (r * y2l_el τ ![0, 1, 0]) =
          r * r * (r⁻¹ * y2l_el τ ![0, 1, 0] * r) * y2l_el τ ![0, 1, 0] := by group
      _ = 1 := by rw [hr2, one_mul, y2l_conj_el, hr, ← y2l_el_add, y2l_vec_v, y2l_el_zero]
  · have h : r * y2l_el τ ![0, 1, 0] * t = r * t * (t⁻¹ * y2l_el τ ![0, 1, 0] * t) := by group
    rw [h, y2l_conj_el, ht, y2l_vec_RS, y2l_pow4_mul_el τ hs, y2l_norm_vec]

theorem y2l_e_of_pow4 {s : X} {k : ZMod 4} (hs : s ^ 4 = y2l_el τ ![k, 0, k])
    (hk : k = 0 ∨ k = 1) :
    ∃ e : Bool, s ^ 4 = if e then y2l_el τ ![1, 0, 0] * y2l_el τ ![0, 0, 1] else 1 := by
  rcases hk with rfl | rfl
  · refine ⟨false, ?_⟩
    rw [hs, if_neg Bool.false_ne_true]
    exact (y2l_el_eq_one_iff τ _).mpr (by decide)
  · refine ⟨true, ?_⟩
    rw [hs, if_pos rfl, ← y2l_el_add]
    congr 1
    decide

theorem y2l_exists_rels (hC : centralizer (M : Set X) = M) {xa xb : X}
    (ha : y2l_rho τ xa = y2l_dec y2l_alpha0) (hb : y2l_rho τ xb = y2l_dec y2l_beta0) :
    ∃ (e : Bool) (r s : X),
      Y2LRels 2 e (y2l_el τ ![1, 0, 0]) (y2l_el τ ![0, 1, 0]) (y2l_el τ ![0, 0, 1]) r s := by
  obtain ⟨r, t, hr, ht, hr2, ht2⟩ := y2l_exists_frame τ hC ha hb
  have hs : y2l_rho τ (r * t) = y2l_dec y2l_S0 := by
    rw [map_mul, hr, ht, ← y2l_dec_mul3, y2l_mul3_RS]
  obtain ⟨k, hk⟩ := y2l_pow4_of_rho τ hC hs
  rcases y2l_zmod4_cases k with h01 | h23
  · obtain ⟨e, he⟩ := y2l_e_of_pow4 τ hk h01
    exact ⟨e, r, r * t, y2l_rels_of_frame τ hr ht hr2 ht2 he⟩
  · obtain ⟨h1, h2, h3⟩ := y2l_adjust τ hr ht hr2
    have hk' : (r * y2l_el τ ![0, 1, 0] * t) ^ 4 = y2l_el τ ![k + 2, 0, k + 2] := by
      rw [h3, hk, ← y2l_el_add, y2l_add_202]
    obtain ⟨e, he⟩ := y2l_e_of_pow4 τ hk' h23
    exact ⟨e, _, _, y2l_rels_of_frame τ h1 ht h2 ht2 he⟩

theorem y2l_el_basis (a b c : ℕ) :
    y2l_el τ ![1, 0, 0] ^ a * y2l_el τ ![0, 1, 0] ^ b * y2l_el τ ![0, 0, 1] ^ c =
      y2l_el τ ![(a : ZMod 4), (b : ZMod 4), (c : ZMod 4)] := by
  rw [← y2l_el_nsmul, ← y2l_el_nsmul, ← y2l_el_nsmul, ← y2l_el_add, ← y2l_el_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem y2l_seven (r s : X) : ∀ y ∈ y2l_ws7 2, FreeGroup.lift
    (![y2l_el τ ![1, 0, 0], y2l_el τ ![0, 1, 0], y2l_el τ ![0, 0, 1], r, s] : Fin 5 → X)
    (FreeGroup.mk y) ≠ 1 := by
  have key : ∀ t ∈ ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
      List (ℕ × ℕ × ℕ)), (![((2 * t.1 : ℕ) : ZMod 4), ((2 * t.2.1 : ℕ) : ZMod 4),
        ((2 * t.2.2 : ℕ) : ZMod 4)] : Fin 3 → ZMod 4) ≠ 0 := by
    decide
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  rw [y2l_lift_ws7_word]
  show y2l_el τ ![1, 0, 0] ^ (2 * t.1) * y2l_el τ ![0, 1, 0] ^ (2 * t.2.1) *
    y2l_el τ ![0, 0, 1] ^ (2 * t.2.2) ≠ 1
  rw [y2l_el_basis, Ne, y2l_el_eq_one_iff]
  exact key t ht

theorem y2l_closure_el :
    closure ({y2l_el τ ![1, 0, 0], y2l_el τ ![0, 1, 0], y2l_el τ ![0, 0, 1]} : Set X) = M := by
  refine le_antisymm ((closure_le _).mpr ?_) fun m hm => ?_
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> exact y2l_el_mem τ _
  · obtain ⟨c, rfl⟩ := y2l_exists_el τ hm
    have hc : c = ![((c 0).val : ZMod 4), ((c 1).val : ZMod 4), ((c 2).val : ZMod 4)] := by
      funext i
      fin_cases i <;> simp [ZMod.natCast_zmod_val]
    rw [hc, ← y2l_el_basis]
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
