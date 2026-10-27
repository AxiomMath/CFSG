module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveDefs

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G] {P S : Subgroup G} {s x : G} {a : ℕ}

theorem klein_cases (k u w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    u = 1 ∨ w = 1 ∨ u = w ∨ k = 1 ∨ k = u ∨ k = w ∨ k = u * w := by
  revert k u w
  decide

namespace QData

theorem P_mul_self (h : QData P S s x a) : ∀ p ∈ P, p * p = 1 := by
  obtain ⟨eP⟩ := h.P_klein
  intro p hp
  have h1 : (⟨p, hp⟩ : P) * ⟨p, hp⟩ = 1 := eP.injective (by
    rw [map_mul, map_one]
    generalize eP ⟨p, hp⟩ = u
    revert u
    decide)
  exact congrArg Subtype.val h1

theorem P_comm (h : QData P S s x a) : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
  obtain ⟨eP⟩ := h.P_klein
  intro p hp q hq
  have h1 : (⟨p, hp⟩ : P) * ⟨q, hq⟩ = ⟨q, hq⟩ * ⟨p, hp⟩ :=
    eP.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h1

theorem P_eq_cases (h : QData P S s x a) {u w : G} (hu : u ∈ P) (hw : w ∈ P) (hu1 : u ≠ 1)
    (hw1 : w ≠ 1) (huw : u ≠ w) {p : G} (hp : p ∈ P) :
    p = 1 ∨ p = u ∨ p = w ∨ p = u * w := by
  obtain ⟨eP⟩ := h.P_klein
  have hinj : ∀ {b c : P}, (b : G) ≠ c → eP b ≠ eP c := fun hbc e =>
    hbc (congrArg Subtype.val (eP.injective e))
  have hval : ∀ {b c : P}, eP b = eP c → (b : G) = c := fun e =>
    congrArg Subtype.val (eP.injective e)
  rcases (((klein_cases (eP ⟨p, hp⟩) (eP ⟨u, hu⟩) (eP ⟨w, hw⟩)).resolve_left
      (by rw [← map_one eP]; exact hinj hu1)).resolve_left
      (by rw [← map_one eP]; exact hinj hw1)).resolve_left (hinj huw) with e | e | e | e
  · exact Or.inl (hval (e.trans (map_one eP).symm))
  · exact Or.inr (Or.inl (hval e))
  · exact Or.inr (Or.inr (Or.inl (hval e)))
  · exact Or.inr (Or.inr (Or.inr (hval (e.trans (map_mul eP _ _).symm))))

theorem isOfFinOrder_s (h : QData P S s x a) : IsOfFinOrder s :=
  orderOf_pos_iff.1 (by rw [h.orderOf_s]; positivity)

theorem s_mem (h : QData P S s x a) : s ∈ S := h.S_eq ▸ mem_zpowers s

theorem mem_S_iff (h : QData P S s x a) (u : G) : u ∈ S ↔ ∃ j : ℕ, u = s ^ j := by
  rw [h.S_eq, ← h.isOfFinOrder_s.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, hj.symm⟩, fun ⟨j, hj⟩ => ⟨j, hj.symm⟩⟩

theorem P_comm_S (h : QData P S s x a) : ∀ p ∈ P, ∀ u ∈ S, p * u = u * p := by
  intro p hp u hu
  obtain ⟨j, rfl⟩ := (h.mem_S_iff u).1 hu
  exact ((show Commute p s from h.P_comm_s p hp).pow_right j).eq

theorem conj_conj (h : QData P S s x a) (b : G) : x * (x * b * x⁻¹) * x⁻¹ = b := by
  calc x * (x * b * x⁻¹) * x⁻¹ = (x * x) * b * (x * x)⁻¹ := by group
    _ = b := by rw [h.x_mul_x]; group

theorem exists_lambda (h : QData P S s x a) :
    ∃ l : ℕ, x * s * x⁻¹ = s ^ l ∧ Odd l ∧ Nat.ModEq (2 ^ a) (l * l) 1 := by
  obtain ⟨l, hl⟩ := (h.mem_S_iff _).1 h.x_normalizes_S
  have hll : s ^ (l * l) = s ^ 1 := by
    calc s ^ (l * l) = (x * s * x⁻¹) ^ l := by rw [pow_mul, hl]
      _ = x * (x * s * x⁻¹) * x⁻¹ := by rw [conj_pow, hl]
      _ = s ^ 1 := by rw [h.conj_conj, pow_one]
  have hmod : Nat.ModEq (2 ^ a) (l * l) 1 := h.orderOf_s ▸ pow_eq_pow_iff_modEq.1 hll
  have h2 : Nat.ModEq 2 (l * l) 1 :=
    Nat.ModEq.of_dvd (dvd_pow_self 2 (by have := h.two_le; omega)) hmod
  exact ⟨l, hl, (Nat.odd_mul.1 (Nat.odd_iff.2 h2)).1, hmod⟩

theorem conj_pow_s {l : ℕ} (hl : x * s * x⁻¹ = s ^ l) (j : ℕ) :
    x * s ^ j * x⁻¹ = s ^ (l * j) := by
  rw [← conj_pow, hl, ← pow_mul]

theorem exists_v (h : QData P S s x a) :
    ∃ v p₀ : G, v ∈ P ∧ p₀ ∈ P ∧ v ≠ 1 ∧ p₀ ≠ 1 ∧ v ≠ p₀ ∧ x * v * x⁻¹ = v ∧
      x * p₀ * x⁻¹ = v * p₀ ∧ ∀ p ∈ P, p = 1 ∨ p = v ∨ p = p₀ ∨ p = v * p₀ := by
  obtain ⟨p₀, hp₀P, hp₀⟩ := h.x_acts_nontrivially
  have hqP : x * p₀ * x⁻¹ ∈ P := h.x_normalizes_P p₀ hp₀P
  have hp₀2 : p₀ * p₀ = 1 := h.P_mul_self p₀ hp₀P
  have hcomm : p₀ * (x * p₀ * x⁻¹) = (x * p₀ * x⁻¹) * p₀ := h.P_comm _ hp₀P _ hqP
  have hvx : x * (p₀ * (x * p₀ * x⁻¹)) * x⁻¹ = p₀ * (x * p₀ * x⁻¹) := by
    calc x * (p₀ * (x * p₀ * x⁻¹)) * x⁻¹
        = (x * p₀ * x⁻¹) * (x * (x * p₀ * x⁻¹) * x⁻¹) := by group
      _ = (x * p₀ * x⁻¹) * p₀ := by rw [h.conj_conj]
      _ = p₀ * (x * p₀ * x⁻¹) := hcomm.symm
  have hvP : p₀ * (x * p₀ * x⁻¹) ∈ P := P.mul_mem hp₀P hqP
  have hv1 : p₀ * (x * p₀ * x⁻¹) ≠ 1 := fun e => hp₀ (by
    rw [← inv_eq_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right hp₀2])
  have hp₀1 : p₀ ≠ 1 := by
    rintro rfl
    exact hp₀ (by group)
  have hvp₀ : p₀ * (x * p₀ * x⁻¹) ≠ p₀ := fun e => hp₀ (by rw [e] at hvx; exact hvx)
  refine ⟨_, p₀, hvP, hp₀P, hv1, hp₀1, hvp₀, hvx, ?_,
    fun p hp => h.P_eq_cases hvP hp₀P hv1 hp₀1 hvp₀ hp⟩
  calc x * p₀ * x⁻¹ = (x * p₀ * x⁻¹) * (p₀ * p₀) := by rw [hp₀2, mul_one]
    _ = p₀ * (x * p₀ * x⁻¹) * p₀ := by rw [hcomm]; simp only [mul_assoc]

theorem P_le_normalizer_S (h : QData P S s x a) : P ≤ normalizer (S : Set G) :=
  le_trans (fun p hp => mem_centralizer_iff.2 fun u hu => (h.P_comm_S p hp u hu).symm)
    (centralizer_le_normalizer _)

theorem mem_PS_iff (h : QData P S s x a) (b : G) :
    b ∈ P ⊔ S ↔ ∃ p ∈ P, ∃ j : ℕ, b = p * s ^ j := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P S h.P_le_normalizer_S,
    Set.mem_mul]
  simp only [SetLike.mem_coe]
  constructor
  · rintro ⟨p, hp, u, hu, rfl⟩
    obtain ⟨j, rfl⟩ := (h.mem_S_iff u).1 hu
    exact ⟨p, hp, j, rfl⟩
  · rintro ⟨p, hp, j, rfl⟩
    exact ⟨p, hp, s ^ j, (h.mem_S_iff _).2 ⟨j, rfl⟩, rfl⟩

theorem mul_pow_mem_PS (h : QData P S s x a) {p : G} (hp : p ∈ P) (j : ℕ) :
    p * s ^ j ∈ P ⊔ S :=
  (h.mem_PS_iff _).2 ⟨p, hp, j, rfl⟩

theorem conj_mem_PS (h : QData P S s x a) {b : G} (hb : b ∈ P ⊔ S) : x * b * x⁻¹ ∈ P ⊔ S := by
  obtain ⟨p, hp, j, rfl⟩ := (h.mem_PS_iff b).1 hb
  rw [show x * (p * s ^ j) * x⁻¹ = (x * p * x⁻¹) * (x * s * x⁻¹) ^ j by
    rw [conj_pow]; group]
  exact mul_mem (mem_sup_left (h.x_normalizes_P p hp))
    (mem_sup_right (pow_mem h.x_normalizes_S j))

theorem x_mem_normalizer_PS (h : QData P S s x a) :
    x ∈ normalizer ((P ⊔ S : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro b
  refine ⟨h.conj_mem_PS, fun hb => ?_⟩
  have := h.conj_mem_PS hb
  rwa [h.conj_conj] at this

theorem x_ne_one (h : QData P S s x a) : x ≠ 1 := by
  rintro rfl
  exact h.x_not_mem (one_mem _)

theorem orderOf_x (h : QData P S s x a) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq, h.x_mul_x]) h.x_ne_one

theorem mem_zpowers_x_iff (h : QData P S s x a) (y : G) : y ∈ zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_mod_orderOf, h.orderOf_x]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [Nat.cast_ofNat, h0, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem mem_group_iff (h : QData P S s x a) (q : G) :
    q ∈ QData.group P S x ↔ ∃ p ∈ P, ∃ j e : ℕ, e < 2 ∧ q = p * s ^ j * x ^ e := by
  rw [QData.group, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left (P ⊔ S) (zpowers x) (zpowers_le.2 h.x_mem_normalizer_PS),
    Set.mem_mul]
  simp only [SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, y, hy, rfl⟩
    obtain ⟨p, hp, j, rfl⟩ := (h.mem_PS_iff b).1 hb
    rcases (h.mem_zpowers_x_iff y).1 hy with rfl | rfl
    · exact ⟨p, hp, j, 0, by norm_num, by rw [pow_zero]⟩
    · exact ⟨p, hp, j, 1, by norm_num, by rw [pow_one]⟩
  · rintro ⟨p, hp, j, e, -, rfl⟩
    exact ⟨p * s ^ j, h.mul_pow_mem_PS hp j, x ^ e, pow_mem (mem_zpowers x) e, rfl⟩

theorem PS_inf_zpowers_x (h : QData P S s x a) : (P ⊔ S) ⊓ zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy, hyx⟩
  rcases (h.mem_zpowers_x_iff y).1 hyx with rfl | rfl
  · exact one_mem _
  · exact absurd hy h.x_not_mem

theorem fixed_eq_one_or_eq (h : QData P S s x a) {v : G} (hvP : v ∈ P) (hv1 : v ≠ 1)
    (hvx : x * v * x⁻¹ = v) {w : G} (hwP : w ∈ P) (hwx : x * w * x⁻¹ = w) :
    w = 1 ∨ w = v := by
  obtain ⟨v₀, p₀, hv₀P, hp₀P, hv₀1, -, -, hv₀x, hp₀x, hPelts⟩ := h.exists_v
  have key : ∀ u ∈ P, x * u * x⁻¹ = u → u = 1 ∨ u = v₀ := by
    intro u hu hux
    rcases hPelts u hu with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      rw [e, hp₀x] at hux
      exact hv₀1 (mul_eq_right.1 hux)
    · exfalso
      rw [e, show x * (v₀ * p₀) * x⁻¹ = (x * v₀ * x⁻¹) * (x * p₀ * x⁻¹) by group, hv₀x, hp₀x,
        ← mul_assoc, h.P_mul_self v₀ hv₀P, one_mul] at hux
      exact hv₀1 (mul_eq_right.1 hux.symm)
  rcases key v hvP hvx with e | e
  · exact absurd e hv1
  · rw [e]
    exact key w hwP hwx

theorem comm_factor_cases (h : QData P S s x a) {v : G} (hvP : v ∈ P) (hv1 : v ≠ 1)
    (hvx : x * v * x⁻¹ = v) {p : G} (hp : p ∈ P) :
    p * (x * p * x⁻¹) = 1 ∨ p * (x * p * x⁻¹) = v := by
  have hxp : x * p * x⁻¹ ∈ P := h.x_normalizes_P p hp
  refine h.fixed_eq_one_or_eq hvP hv1 hvx (P.mul_mem hp hxp) ?_
  calc x * (p * (x * p * x⁻¹)) * x⁻¹ = (x * p * x⁻¹) * (x * (x * p * x⁻¹) * x⁻¹) := by group
    _ = (x * p * x⁻¹) * p := by rw [h.conj_conj]
    _ = p * (x * p * x⁻¹) := h.P_comm _ hxp _ hp

theorem sq_PS (h : QData P S s x a) {p : G} (hp : p ∈ P) (j : ℕ) :
    (p * s ^ j) * (p * s ^ j) = s ^ (2 * j) := by
  calc (p * s ^ j) * (p * s ^ j) = p * (s ^ j * p) * s ^ j := by simp only [mul_assoc]
    _ = p * (p * s ^ j) * s ^ j := by rw [← h.P_comm_S p hp _ (pow_mem h.s_mem j)]
    _ = (p * p) * (s ^ j * s ^ j) := by simp only [mul_assoc]
    _ = s ^ (2 * j) := by rw [h.P_mul_self p hp, one_mul, ← pow_add, two_mul]

theorem sq_outer (h : QData P S s x a) {l : ℕ} (hl : x * s * x⁻¹ = s ^ l) {p : G} (hp : p ∈ P)
    (j : ℕ) : (p * s ^ j * x) * (p * s ^ j * x) = (p * (x * p * x⁻¹)) * s ^ (j + l * j) := by
  have hxp : x * p * x⁻¹ ∈ P := h.x_normalizes_P p hp
  calc (p * s ^ j * x) * (p * s ^ j * x)
      = p * s ^ j * ((x * p * x⁻¹) * (x * s ^ j * x⁻¹)) * (x * x) := by group
    _ = p * (s ^ j * (x * p * x⁻¹)) * s ^ (l * j) := by
        rw [conj_pow_s hl, h.x_mul_x]; simp only [mul_one, mul_assoc]
    _ = p * ((x * p * x⁻¹) * s ^ j) * s ^ (l * j) := by
        rw [h.P_comm_S _ hxp _ (pow_mem h.s_mem j)]
    _ = (p * (x * p * x⁻¹)) * s ^ (j + l * j) := by rw [pow_add]; simp only [mul_assoc]

end QData

end CFSG.OddStandard
