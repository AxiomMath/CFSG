module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup

section Gen2

variable {G : Type*} [Group G]

@[expose] noncomputable def cc3 (a u v : G) : ℕ :=
  Nat.card {c : G // c * a = a * c ∧ c * u = u * c ∧ c * v = v * c}

theorem cc3_eq_ccard {a u v : G} {B : Type*} [Group B] (e : ↥(centralizer ({a} : Set G)) ≃* B)
    (hu : u ∈ centralizer ({a} : Set G)) (hv : v ∈ centralizer ({a} : Set G)) :
    cc3 a u v = ccard B (e ⟨u, hu⟩) (e ⟨v, hv⟩) := by
  unfold cc3 ccard
  refine Nat.card_congr ?_
  have key : ∀ (c : G) (hc : c ∈ centralizer ({a} : Set G)),
      (c * u = u * c) ↔ (e ⟨c, hc⟩ * e ⟨u, hu⟩ = e ⟨u, hu⟩ * e ⟨c, hc⟩) := by
    intro c hc
    rw [← map_mul, ← map_mul, e.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have key' : ∀ (c : G) (hc : c ∈ centralizer ({a} : Set G)),
      (c * v = v * c) ↔ (e ⟨c, hc⟩ * e ⟨v, hv⟩ = e ⟨v, hv⟩ * e ⟨c, hc⟩) := by
    intro c hc
    rw [← map_mul, ← map_mul, e.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine
    { toFun := fun c => ⟨e ⟨c.1, mem_centralizer_singleton_iff.2 c.2.1⟩,
        (key c.1 _).1 c.2.2.1, (key' c.1 _).1 c.2.2.2⟩
      invFun := fun b => ⟨(e.symm b.1 : G), mem_centralizer_singleton_iff.1 (e.symm b.1).2, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have := (key (e.symm b.1 : G) (e.symm b.1).2).2 (by simpa using b.2.1)
    exact this
  · have := (key' (e.symm b.1 : G) (e.symm b.1).2).2 (by simpa using b.2.2)
    exact this
  · intro c
    ext
    simp
  · intro b
    ext
    simp

theorem ccard_conj (M : Type*) [Group M] (k u v : M) :
    ccard M (k * u * k⁻¹) (k * v * k⁻¹) = ccard M u v := by
  unfold ccard
  refine Nat.card_congr ?_
  refine
    { toFun := fun c => ⟨k⁻¹ * c.1 * k, ?_, ?_⟩
      invFun := fun c => ⟨k * c.1 * k⁻¹, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := c.2.1
    calc k⁻¹ * c.1 * k * u = k⁻¹ * (c.1 * (k * u * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * u * k⁻¹) * c.1) * k := by rw [h1]
      _ = u * (k⁻¹ * c.1 * k) := by group
  · have h1 := c.2.2
    calc k⁻¹ * c.1 * k * v = k⁻¹ * (c.1 * (k * v * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * v * k⁻¹) * c.1) * k := by rw [h1]
      _ = v * (k⁻¹ * c.1 * k) := by group
  · have h1 := c.2.1
    calc k * c.1 * k⁻¹ * (k * u * k⁻¹) = k * (c.1 * u) * k⁻¹ := by group
      _ = k * (u * c.1) * k⁻¹ := by rw [h1]
      _ = (k * u * k⁻¹) * (k * c.1 * k⁻¹) := by group
  · have h1 := c.2.2
    calc k * c.1 * k⁻¹ * (k * v * k⁻¹) = k * (c.1 * v) * k⁻¹ := by group
      _ = k * (v * c.1) * k⁻¹ := by rw [h1]
      _ = (k * v * k⁻¹) * (k * c.1 * k⁻¹) := by group
  · intro c; ext; simp [mul_assoc]
  · intro c; ext; simp [mul_assoc]

theorem ccard_pos (M : Type*) [Group M] [Finite M] (u v : M) : 0 < ccard M u v := by
  unfold ccard
  have : Nonempty {c : M // c * u = u * c ∧ c * v = v * c} := ⟨⟨1, by simp, by simp⟩⟩
  exact Nat.card_pos

theorem two_pow_le_64 {m n : ℕ} (hn : n = 288 ∨ n = 72 ∨ n = 576 ∨ (0 < n ∧ n ≤ 36))
    (hdvd : 2 ^ m ∣ n) : 2 ^ m ≤ 64 := by
  by_contra hlt0
  have hlt : 64 < 2 ^ m := not_le.mp hlt0
  have hm : 7 ≤ m := by
    by_contra h0
    have h : m < 7 := not_le.mp h0
    have : 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h128 : 2 ^ 7 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm
  have h2 := h128.trans hdvd
  rcases hn with rfl | rfl | rfl | ⟨h0, h36⟩
  · revert h2; decide
  · revert h2; decide
  · revert h2; decide
  · have := Nat.le_of_dvd h0 h2
    omega


theorem exists_central_involution_of_pgroup [Finite G] (P : Subgroup G) (hP : IsPGroup 2 P)
    (hP1 : ¬ Nat.card P = 1) :
    ∃ w : G, w ∈ P ∧ orderOf w = 2 ∧ ∀ p ∈ P, p * w = w * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial P := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hP1 (Nat.card_eq_one_iff_unique.2 ⟨hn, inferInstance⟩)
  have hZnt := hP.center_nontrivial
  have hZ : IsPGroup 2 (center P) := hP.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card_iff_nontrivial.2 hZnt
    rw [pow_zero] at hn
    omega
  have h2 : 2 ∣ Nat.card (center P) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨w0, hw0⟩ := exists_prime_orderOf_dvd_card' (p := 2) h2
  refine ⟨((w0 : P) : G), (w0 : P).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hw0
  · intro p hp
    have := Subgroup.mem_center_iff.1 w0.2 ⟨p, hp⟩
    exact congrArg Subtype.val this

end Gen2

end CFSG.GH74.GLS.C3.Prop121.Card7
