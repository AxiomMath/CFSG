module

public import CFSG.GH74.GLS.Stage4.RestRoot
public import CFSG.GH74.GLS.Stage4.Statements

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair

variable {G : Type} [Group G]

namespace DodecA

@[expose] def HInv (H A : Subgroup G) : Prop := ∀ h ∈ H, ∀ x ∈ A, h * x * h⁻¹ ∈ A

variable {H A B : Subgroup G}

theorem conjBy_eq_of_mem (hA : HInv H A) {h : G} (hh : h ∈ H) : conjBy h A = A := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    simpa [mul_assoc] using hA h⁻¹ (H.inv_mem hh) _ hx
  · intro hx
    exact hA h hh x hx

theorem HInv.map_conjBy (hA : HInv H A) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    HInv H (conjBy g A) := by
  intro h hh x hx
  rw [mem_conjBy_iff] at hx ⊢
  have h1 : g * h * g⁻¹ ∈ H := (mem_normalizer_iff.1 hg h).1 hh
  have e : g * (h * x * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
  rw [e]
  exact hA _ h1 _ hx

theorem conjBy_mul_of_mem (hA : HInv H A) {g h : G} (hg : g ∈ normalizer (H : Set G)) (hh : h ∈ H) :
    conjBy (g * h) A = conjBy g A := by
  rw [BNPair.conjBy_mul, conjBy_eq_of_mem (hA.map_conjBy hg) hh]

theorem conjBy_eq_self_of_comm {c : G} (hc : ∀ x ∈ A, c * x = x * c) : conjBy c A = A := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have h1 := hc _ hx
    have h2 : c * (c * x * c⁻¹) = c * x := by
      rw [h1]
      group
    have h3 : c * x * c⁻¹ = x := mul_left_cancel h2
    rwa [h3] at hx
  · intro hx
    have h1 := hc _ hx
    have h2 : c * x * c⁻¹ = x := by
      rw [h1]
      group
    rwa [h2]

theorem conjBy_eq_of_swap {w : G} (hww : w * w ∈ H) (hB : HInv H B)
    (hAB : ∀ x ∈ A, w * x * w⁻¹ ∈ B) (hBA : ∀ x ∈ B, w * x * w⁻¹ ∈ A) : conjBy w A = B := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have h1 := hAB _ hx
    have h2 := hB (w * w)⁻¹ (H.inv_mem hww) _ h1
    have e : (w * w)⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * ((w * w)⁻¹)⁻¹ = x := by group
    rwa [e] at h2
  · intro hx
    exact hBA x hx

theorem conjBy_inv_eq (hA : HInv H A) {w : G} (hw : w ∈ normalizer (H : Set G)) (hww : w * w ∈ H) :
    conjBy w⁻¹ A = conjBy w A := by
  have e : w * (w * w)⁻¹ = w⁻¹ := by group
  rw [← e]
  exact conjBy_mul_of_mem hA hw (H.inv_mem hww)

theorem conjBy_pow_add (g : G) (m n : ℕ) (B : Subgroup G) :
    conjBy (g ^ m) (conjBy (g ^ n) B) = conjBy (g ^ (n + m)) B := by
  rw [← BNPair.conjBy_mul, ← pow_add]

theorem conjBy_pow_mod (hB : HInv H B) {g : G} (hg : g ∈ normalizer (H : Set G)) (hg3 : g ^ 3 ∈ H)
    (k : ℕ) : conjBy (g ^ k) B = conjBy (g ^ (k % 3)) B := by
  have e : g ^ k = g ^ (k % 3) * (g ^ 3) ^ (k / 3) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e]
  exact conjBy_mul_of_mem hB (pow_mem hg _) (pow_mem hg3 _)

theorem conjBy_w_conjBy_a (hA : HInv H A) {w a : G} (hw : w ∈ normalizer (H : Set G))
    (ha : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H) (hwa : ∃ h ∈ H, w * a * w⁻¹ = a⁻¹ * h) :
    conjBy w⁻¹ (conjBy a A) = conjBy (a ^ 2) (conjBy w⁻¹ A) := by
  obtain ⟨h₁, hh₁, hrel⟩ := hwa
  have e : a * w⁻¹ = (w⁻¹ * a ^ 2) * ((a ^ 3)⁻¹ * h₁) := by
    calc a * w⁻¹ = w⁻¹ * (w * a * w⁻¹) := by group
      _ = w⁻¹ * (a⁻¹ * h₁) := by rw [hrel]
      _ = (w⁻¹ * a ^ 2) * ((a ^ 3)⁻¹ * h₁) := by group
  rw [← BNPair.conjBy_mul, ← BNPair.conjBy_mul, e]
  exact conjBy_mul_of_mem hA (mul_mem (inv_mem hw) (pow_mem ha 2)) (mul_mem (inv_mem ha3) hh₁)

theorem conjBy_w_conjBy_a_pow (hA : HInv H A) {w a : G} (hw : w ∈ normalizer (H : Set G))
    (ha : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H) (hwa : ∃ h ∈ H, w * a * w⁻¹ = a⁻¹ * h)
    (k : ℕ) : conjBy w⁻¹ (conjBy (a ^ k) A) = conjBy (a ^ (2 * k)) (conjBy w⁻¹ A) := by
  induction k with
  | zero => simp [BNPair.conjBy_one]
  | succ k ih =>
    have hk : HInv H (conjBy (a ^ k) A) := hA.map_conjBy (pow_mem ha k)
    have e1 : conjBy (a ^ (k + 1)) A = conjBy a (conjBy (a ^ k) A) := by
      rw [pow_succ, BNPair.conjBy_mul]
    calc conjBy w⁻¹ (conjBy (a ^ (k + 1)) A) = conjBy w⁻¹ (conjBy a (conjBy (a ^ k) A)) := by
          rw [e1]
      _ = conjBy (a ^ 2) (conjBy w⁻¹ (conjBy (a ^ k) A)) := conjBy_w_conjBy_a hk hw ha ha3 hwa
      _ = conjBy (a ^ 2) (conjBy (a ^ (2 * k)) (conjBy w⁻¹ A)) := by rw [ih]
      _ = conjBy (a ^ (2 * k + 2)) (conjBy w⁻¹ A) := conjBy_pow_add _ _ _ _
      _ = conjBy (a ^ (2 * (k + 1))) (conjBy w⁻¹ A) := by rw [mul_add, mul_one]

theorem comm_conjBy {g : G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ conjBy g A, ∀ y ∈ conjBy g A, x * y = y * x := by
  intro x hx y hy
  rw [mem_conjBy_iff] at hx hy
  have h := hA _ hx _ hy
  have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have e2 : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
  rw [e1, e2] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem exp_conjBy {p : ℕ} {g : G} (hA : ∀ x ∈ A, x ^ p = 1) : ∀ x ∈ conjBy g A, x ^ p = 1 := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have h := hA _ hx
  rw [conj_pow, conj_eq_one_iff] at h
  exact h

theorem conjBy_ne_bot {g : G} (hA : A ≠ ⊥) : conjBy g A ≠ ⊥ := fun h =>
  hA ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) A
    (MulAut.conj g⁻¹).injective).1 h)

theorem card_conjBy (g : G) (A : Subgroup G) : Nat.card ↥(conjBy g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isRoot6_cases {i : ℤ} (hi : IsRoot 6 i) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = -1 ∨ i = -2 ∨ i = -3 ∨ i = -4 ∨ i = -5 ∨
      i = -6 := by
  obtain ⟨h0, h1⟩ := hi
  omega

theorem ne_bot_of_card {X : Subgroup G} {q : ℕ} (hq : 2 ≤ q) (hX : Nat.card ↥X = q) : X ≠ ⊥ := by
  intro hb
  rw [← Subgroup.card_eq_one] at hb
  omega

theorem dodec_cube {Q : Type*} [Group Q] {A W₁ W₂ : Q} (hA : A ^ 3 = 1)
    (h1 : W₁ * A * W₁⁻¹ = A⁻¹) (h2 : W₂ * A * W₂⁻¹ = A⁻¹) (hs1 : W₁ * W₁ = 1) (hs2 : W₂ * W₂ = 1)
    (hc : W₁ * W₂ = W₂ * W₁) :
    (W₁ * (A⁻¹ * W₂ * A)) ^ 3 = W₁ * W₂ ∧ (W₁ * (A⁻¹ * W₂ * A)) ^ 6 = 1 := by
  have f1 : W₁ * A⁻¹ = A * W₁ := by
    calc W₁ * A⁻¹ = (W₁ * A * W₁⁻¹)⁻¹ * W₁ := by group
      _ = A * W₁ := by rw [h1, inv_inv]
  have f2 : W₂ * A = A⁻¹ * W₂ := by
    calc W₂ * A = (W₂ * A * W₂⁻¹) * W₂ := by group
      _ = A⁻¹ * W₂ := by rw [h2]
  have f3 : (W₁ * W₂) * A = A * (W₁ * W₂) := by
    calc (W₁ * W₂) * A = W₁ * (W₂ * A) := by group
      _ = W₁ * (A⁻¹ * W₂) := by rw [f2]
      _ = (W₁ * A⁻¹) * W₂ := by group
      _ = (A * W₁) * W₂ := by rw [f1]
      _ = A * (W₁ * W₂) := by group
  have f4 : W₁ * (A⁻¹ * W₂ * A) = A ^ 2 * (W₁ * W₂) := by
    calc W₁ * (A⁻¹ * W₂ * A) = (W₁ * A⁻¹) * W₂ * A := by group
      _ = (A * W₁) * W₂ * A := by rw [f1]
      _ = A * ((W₁ * W₂) * A) := by group
      _ = A * (A * (W₁ * W₂)) := by rw [f3]
      _ = A ^ 2 * (W₁ * W₂) := by rw [pow_two, mul_assoc]
  have f5 : (W₁ * W₂) ^ 2 = 1 := by
    calc (W₁ * W₂) ^ 2 = W₁ * (W₂ * W₁) * W₂ := by rw [pow_two]; simp only [mul_assoc]
      _ = W₁ * (W₁ * W₂) * W₂ := by rw [hc]
      _ = (W₁ * W₁) * (W₂ * W₂) := by group
      _ = 1 := by rw [hs1, hs2, mul_one]
  have hcomm : Commute (A ^ 2) (W₁ * W₂) := (show Commute A (W₁ * W₂) from f3.symm).pow_left 2
  have hA6 : (A ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hA, one_pow]
  have f6 : (W₁ * (A⁻¹ * W₂ * A)) ^ 3 = W₁ * W₂ := by
    rw [f4, hcomm.mul_pow, hA6, one_mul, pow_succ, f5, one_mul]
  refine ⟨f6, ?_⟩
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, f6, f5]

end DodecA

variable {D : Ch6Notation G}

theorem Ch6Basics.w₁_comm_w₂ (h : Ch6Basics D) : D.w₁ * D.w₂ = D.w₂ * D.w₁ :=
  h.K_comm _ h.w₁_mem _ h.w₂_mem

theorem Ch6Basics.sq₁ (h : Ch6Basics D) : D.w₁ * D.w₁ ∈ D.H := by
  rw [h.w₁_sq]
  exact h.z_mem_H

theorem Ch6Basics.sq₂ (h : Ch6Basics D) : D.r₂ * D.r₂ ∈ D.H := by
  have e : D.r₂ * D.r₂ = D.a⁻¹ * (D.w₂ * D.w₂) * D.a := by
    simp only [Ch6Notation.r₂]
    group
  rw [e, h.w₂_sq]
  have := (mem_normalizer_iff.1 (inv_mem h.a_normH) D.z).1 h.z_mem_H
  simpa using this

theorem Ch6Basics.conj_H₁ (h : Ch6Basics D) : ∀ x ∈ D.H, D.w₁ * x * D.w₁⁻¹ ∈ D.H :=
  fun x hx => (mem_normalizer_iff.1 h.w₁_normH x).1 hx

theorem Ch6Basics.conj_H₂ (h : Ch6Basics D) : ∀ x ∈ D.H, D.r₂ * x * D.r₂⁻¹ ∈ D.H := by
  have hr : D.r₂ ∈ normalizer (D.H : Set G) :=
    mul_mem (mul_mem (inv_mem h.a_normH) h.w₂_normH) h.a_normH
  exact fun x hx => (mem_normalizer_iff.1 hr x).1 hx

namespace DodecA

theorem cube_aux (h : Ch6Basics D) :
    (D.w₁ * D.w₂)⁻¹ * (D.w₁ * D.r₂) ^ 3 ∈ D.H ∧ (D.w₁ * D.r₂) ^ 6 ∈ D.H := by
  have : (D.H.subgroupOf (normalizer (D.H : Set G))).Normal := Subgroup.normal_in_normalizer
  let π : ↥(normalizer (D.H : Set G)) →* ↥(normalizer (D.H : Set G)) ⧸
      D.H.subgroupOf (normalizer (D.H : Set G)) := QuotientGroup.mk' _
  let w₁' : ↥(normalizer (D.H : Set G)) := ⟨D.w₁, h.w₁_normH⟩
  let w₂' : ↥(normalizer (D.H : Set G)) := ⟨D.w₂, h.w₂_normH⟩
  let a' : ↥(normalizer (D.H : Set G)) := ⟨D.a, h.a_normH⟩
  have hπ : ∀ x y : ↥(normalizer (D.H : Set G)), π x = π y ↔ (x : G)⁻¹ * (y : G) ∈ D.H :=
    fun x y => by
      show (QuotientGroup.mk x : _ ⧸ _) = QuotientGroup.mk y ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
  have hπ1 : ∀ x : ↥(normalizer (D.H : Set G)), π x = 1 ↔ (x : G) ∈ D.H := fun x => by
    show (QuotientGroup.mk x : _ ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hA : π a' ^ 3 = 1 := by
    rw [← map_pow π a' 3, hπ1]
    exact h.a_cube
  have hrel : ∀ (w : ↥(normalizer (D.H : Set G))) (h₁ : G), h₁ ∈ D.H →
      (w : G) * D.a * (w : G)⁻¹ = D.a⁻¹ * h₁ → π w * π a' * (π w)⁻¹ = (π a')⁻¹ := by
    intro w h₁ hh₁ hr
    have e : π (w * a' * w⁻¹) = π a'⁻¹ := by
      rw [hπ]
      show ((w : G) * D.a * (w : G)⁻¹)⁻¹ * D.a⁻¹ ∈ D.H
      rw [hr]
      have : (D.a⁻¹ * h₁)⁻¹ * D.a⁻¹ = h₁⁻¹ := by group
      rw [this]
      exact D.H.inv_mem hh₁
    simpa only [map_mul, map_inv] using e
  obtain ⟨h₁, hh₁, hr₁⟩ := h.w₁_a
  obtain ⟨h₂, hh₂, hr₂⟩ := h.w₂_a
  have hsq : ∀ (w : ↥(normalizer (D.H : Set G))), (w : G) * (w : G) ∈ D.H → π w * π w = 1 := by
    intro w hw
    rw [← map_mul, hπ1]
    exact hw
  have hc : π w₁' * π w₂' = π w₂' * π w₁' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h.w₁_comm_w₂
  obtain ⟨k3, k6⟩ := dodec_cube hA (hrel w₁' h₁ hh₁ hr₁) (hrel w₂' h₂ hh₂ hr₂)
    (hsq w₁' h.sq₁) (hsq w₂' (by rw [h.w₂_sq]; exact h.z_mem_H)) hc
  have e3 : π ((w₁' * (a'⁻¹ * w₂' * a')) ^ 3) = π (w₁' * w₂') := by
    simpa only [map_mul, map_inv, map_pow] using k3
  have e6 : π ((w₁' * (a'⁻¹ * w₂' * a')) ^ 6) = 1 := by
    simpa only [map_mul, map_inv, map_pow] using k6
  exact ⟨(hπ _ _).1 e3.symm, (hπ1 _).1 e6⟩

end DodecA

theorem Ch6Basics.pow (h : Ch6Basics D) : (D.w₁ * D.r₂) ^ 6 ∈ D.H :=
  (DodecA.cube_aux h).2

theorem Ch6Basics.cube (h : Ch6Basics D) : ∃ h' ∈ D.H, (D.w₁ * D.r₂) ^ 3 = (D.w₁ * D.w₂) * h' :=
  ⟨_, (DodecA.cube_aux h).1, (mul_inv_cancel_left _ _).symm⟩

namespace DodecA

variable {A : Subgroup G}

theorem w₂_sq_mem (h : Ch6Basics D) : D.w₂ * D.w₂ ∈ D.H := by
  rw [h.w₂_sq]
  exact h.z_mem_H

theorem conjBy_w₁_X₁ (h : Ch6Basics D) : conjBy D.w₁⁻¹ D.X₁ = D.X₁' := by
  rw [conjBy_inv_eq h.H_norm_X₁ h.w₁_normH h.sq₁]
  exact conjBy_eq_of_swap h.sq₁ h.H_norm_X₁' h.w₁_swap h.w₁_swap'

theorem conjBy_w₁_X₁' (h : Ch6Basics D) : conjBy D.w₁⁻¹ D.X₁' = D.X₁ := by
  rw [conjBy_inv_eq h.H_norm_X₁' h.w₁_normH h.sq₁]
  exact conjBy_eq_of_swap h.sq₁ h.H_norm_X₁ h.w₁_swap' h.w₁_swap

theorem conjBy_w₂_X₂ (h : Ch6Basics D) : conjBy D.w₂⁻¹ D.X₂ = D.X₂' := by
  rw [conjBy_inv_eq h.H_norm_X₂ h.w₂_normH (w₂_sq_mem h)]
  exact conjBy_eq_of_swap (w₂_sq_mem h) h.H_norm_X₂' h.w₂_swap h.w₂_swap'

theorem conjBy_w₂_X₂' (h : Ch6Basics D) : conjBy D.w₂⁻¹ D.X₂' = D.X₂ := by
  rw [conjBy_inv_eq h.H_norm_X₂' h.w₂_normH (w₂_sq_mem h)]
  exact conjBy_eq_of_swap (w₂_sq_mem h) h.H_norm_X₂ h.w₂_swap' h.w₂_swap

theorem conjBy_w₁_X₂ (h : Ch6Basics D) : conjBy D.w₁⁻¹ D.X₂ = D.X₂ :=
  conjBy_eq_self_of_comm fun x hx =>
    h.K_comm _ (D.K₁.inv_mem h.w₁_mem) x (by rw [h.K₂_eq]; exact Subgroup.mem_sup_left hx)

theorem conjBy_w₁_X₂' (h : Ch6Basics D) : conjBy D.w₁⁻¹ D.X₂' = D.X₂' :=
  conjBy_eq_self_of_comm fun x hx =>
    h.K_comm _ (D.K₁.inv_mem h.w₁_mem) x (by rw [h.K₂_eq]; exact Subgroup.mem_sup_right hx)

theorem conjBy_w₂_X₁ (h : Ch6Basics D) : conjBy D.w₂⁻¹ D.X₁ = D.X₁ :=
  conjBy_eq_self_of_comm fun x hx =>
    (h.K_comm x (by rw [h.K₁_eq]; exact Subgroup.mem_sup_left hx) _
      (D.K₂.inv_mem h.w₂_mem)).symm

theorem conjBy_w₂_X₁' (h : Ch6Basics D) : conjBy D.w₂⁻¹ D.X₁' = D.X₁' :=
  conjBy_eq_self_of_comm fun x hx =>
    (h.K_comm x (by rw [h.K₁_eq]; exact Subgroup.mem_sup_right hx) _
      (D.K₂.inv_mem h.w₂_mem)).symm

theorem conjBy_r₂ (h : Ch6Basics D) (hA : HInv D.H A) :
    conjBy D.r₂⁻¹ A = conjBy (D.a ^ 2) (conjBy D.w₂⁻¹ A) := by
  obtain ⟨h₂, hh₂, hrel⟩ := h.w₂_a
  have hrel' : D.w₂ * D.a⁻¹ * D.w₂⁻¹ = h₂⁻¹ * D.a := by
    calc D.w₂ * D.a⁻¹ * D.w₂⁻¹ = (D.w₂ * D.a * D.w₂⁻¹)⁻¹ := by group
      _ = (D.a⁻¹ * h₂)⁻¹ := by rw [hrel]
      _ = h₂⁻¹ * D.a := by group
  have e : D.r₂⁻¹ = (D.w₂⁻¹ * D.a ^ 2) * ((D.a ^ 2)⁻¹ * h₂⁻¹ * D.a ^ 2) := by
    calc D.r₂⁻¹ = D.a⁻¹ * D.w₂⁻¹ * D.a := by
          simp only [Ch6Notation.r₂]
          group
      _ = D.w₂⁻¹ * (D.w₂ * D.a⁻¹ * D.w₂⁻¹) * D.a := by group
      _ = D.w₂⁻¹ * (h₂⁻¹ * D.a) * D.a := by rw [hrel']
      _ = (D.w₂⁻¹ * D.a ^ 2) * ((D.a ^ 2)⁻¹ * h₂⁻¹ * D.a ^ 2) := by
          simp only [pow_two]
          group
  have hmem : (D.a ^ 2)⁻¹ * h₂⁻¹ * D.a ^ 2 ∈ D.H := by
    have := (mem_normalizer_iff.1 (inv_mem (pow_mem h.a_normH 2)) h₂⁻¹).1 (D.H.inv_mem hh₂)
    simpa using this
  rw [e, conjBy_mul_of_mem hA (mul_mem (inv_mem h.w₂_normH) (pow_mem h.a_normH 2)) hmem,
    BNPair.conjBy_mul]

theorem act₁_gen (h : Ch6Basics D) {X X' : Subgroup G} (hX : HInv D.H X) (hX' : HInv D.H X')
    (hT : conjBy D.w₁⁻¹ X = X') (k l : ℕ) (hkl : (2 * k) % 3 = l % 3) :
    conjBy D.w₁⁻¹ (conjBy (D.a ^ k) X) = conjBy (D.a ^ l) X' := by
  rw [conjBy_w_conjBy_a_pow hX h.w₁_normH h.a_normH h.a_cube h.w₁_a k, hT,
    conjBy_pow_mod hX' h.a_normH h.a_cube (2 * k), hkl,
    ← conjBy_pow_mod hX' h.a_normH h.a_cube l]

theorem act₂_gen (h : Ch6Basics D) {X X' : Subgroup G} (hX : HInv D.H X) (hX' : HInv D.H X')
    (hT : conjBy D.w₂⁻¹ X = X') (k l : ℕ) (hkl : (2 * k + 2) % 3 = l % 3) :
    conjBy D.r₂⁻¹ (conjBy (D.a ^ k) X) = conjBy (D.a ^ l) X' := by
  have hk : HInv D.H (conjBy (D.a ^ k) X) := hX.map_conjBy (pow_mem h.a_normH k)
  rw [conjBy_r₂ h hk, conjBy_w_conjBy_a_pow hX h.w₂_normH h.a_normH h.a_cube h.w₂_a k, hT,
    conjBy_pow_add, conjBy_pow_mod hX' h.a_normH h.a_cube (2 * k + 2), hkl,
    ← conjBy_pow_mod hX' h.a_normH h.a_cube l]

theorem rootk_p1 (D : Ch6Notation G) : D.root 1 = conjBy (D.a ^ 0) D.X₁ := by
  rw [root_p1, pow_zero, BNPair.conjBy_one]
theorem rootk_p2 (D : Ch6Notation G) : D.root 2 = conjBy (D.a ^ 2) D.X₂' := root_p2 D
theorem rootk_p3 (D : Ch6Notation G) : D.root 3 = conjBy (D.a ^ 1) D.X₁' := by
  rw [root_p3, pow_one]
theorem rootk_p4 (D : Ch6Notation G) : D.root 4 = conjBy (D.a ^ 0) D.X₂ := by
  rw [root_p4, pow_zero, BNPair.conjBy_one]
theorem rootk_p5 (D : Ch6Notation G) : D.root 5 = conjBy (D.a ^ 2) D.X₁ := root_p5 D
theorem rootk_p6 (D : Ch6Notation G) : D.root 6 = conjBy (D.a ^ 1) D.X₂' := by
  rw [root_p6, pow_one]
theorem rootk_m1 (D : Ch6Notation G) : D.root (-1) = conjBy (D.a ^ 0) D.X₁' := by
  rw [root_m1, pow_zero, BNPair.conjBy_one]
theorem rootk_m2 (D : Ch6Notation G) : D.root (-2) = conjBy (D.a ^ 2) D.X₂ := root_m2 D
theorem rootk_m3 (D : Ch6Notation G) : D.root (-3) = conjBy (D.a ^ 1) D.X₁ := by
  rw [root_m3, pow_one]
theorem rootk_m4 (D : Ch6Notation G) : D.root (-4) = conjBy (D.a ^ 0) D.X₂' := by
  rw [root_m4, pow_zero, BNPair.conjBy_one]
theorem rootk_m5 (D : Ch6Notation G) : D.root (-5) = conjBy (D.a ^ 2) D.X₁' := root_m5 D
theorem rootk_m6 (D : Ch6Notation G) : D.root (-6) = conjBy (D.a ^ 1) D.X₂ := by
  rw [root_m6, pow_one]

theorem root_rec (D : Ch6Notation G) (P : Subgroup G → Prop) (hX₁ : P D.X₁) (hX₁' : P D.X₁')
    (hX₂ : P D.X₂) (hX₂' : P D.X₂') (ha : ∀ B, P B → P (conjBy D.a B))
    (ha2 : ∀ B, P B → P (conjBy (D.a ^ 2) B)) {i : ℤ} (hi : IsRoot 6 i) : P (D.root i) := by
  rcases isRoot6_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [root_p1]; exact hX₁
  · rw [root_p2]; exact ha2 _ hX₂'
  · rw [root_p3]; exact ha _ hX₁'
  · rw [root_p4]; exact hX₂
  · rw [root_p5]; exact ha2 _ hX₁
  · rw [root_p6]; exact ha _ hX₂'
  · rw [root_m1]; exact hX₁'
  · rw [root_m2]; exact ha2 _ hX₂
  · rw [root_m3]; exact ha _ hX₁
  · rw [root_m4]; exact hX₂'
  · rw [root_m5]; exact ha2 _ hX₁'
  · rw [root_m6]; exact ha _ hX₂

end DodecA

theorem Ch6Basics.invariant (h : Ch6Basics D) :
    ∀ i : ℤ, IsRoot 6 i → ∀ x ∈ D.H, ∀ y ∈ D.root i, x * y * x⁻¹ ∈ D.root i := fun _ hi =>
  DodecA.root_rec D (DodecA.HInv D.H) h.H_norm_X₁ h.H_norm_X₁' h.H_norm_X₂ h.H_norm_X₂'
    (fun _ hB => hB.map_conjBy h.a_normH) (fun _ hB => hB.map_conjBy (pow_mem h.a_normH 2)) hi

theorem Ch6Basics.root_comm (h : Ch6Basics D) :
    ∀ i : ℤ, IsRoot 6 i → ∀ x ∈ D.root i, ∀ y ∈ D.root i, x * y = y * x := fun _ hi =>
  DodecA.root_rec D (fun B => ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) h.X₁_comm h.X₁'_comm h.X₂_comm
    h.X₂'_comm (fun _ hB => DodecA.comm_conjBy hB) (fun _ hB => DodecA.comm_conjBy hB) hi

theorem Ch6Basics.root_exp (h : Ch6Basics D) :
    ∀ i : ℤ, IsRoot 6 i → ∀ x ∈ D.root i, x ^ D.p = 1 := fun _ hi =>
  DodecA.root_rec D (fun B => ∀ x ∈ B, x ^ D.p = 1) h.X₁_exp h.X₁'_exp h.X₂_exp h.X₂'_exp
    (fun _ hB => DodecA.exp_conjBy hB) (fun _ hB => DodecA.exp_conjBy hB) hi

theorem Ch6Basics.root_ne_bot (h : Ch6Basics D) : ∀ i : ℤ, IsRoot 6 i → D.root i ≠ ⊥ := fun _ hi =>
  DodecA.root_rec D (fun B => B ≠ ⊥)
    (DodecA.ne_bot_of_card (by have := h.q₁_ge; omega) h.card_X₁)
    (DodecA.ne_bot_of_card (by have := h.q₁_ge; omega) h.card_X₁')
    (DodecA.ne_bot_of_card (by have := h.q₂_ge; omega) h.card_X₂)
    (DodecA.ne_bot_of_card (by have := h.q₂_ge; omega) h.card_X₂')
    (fun _ hB => DodecA.conjBy_ne_bot hB) (fun _ hB => DodecA.conjBy_ne_bot hB) hi

theorem Ch6Basics.rootOrdersG2 (h : Ch6Basics D) (hq : D.q₁ = D.q₂) :
    RootOrdersG2 D.root D.q₂ := by
  intro i h1 h6
  interval_cases i
  · rw [root_p1, h.card_X₁, hq]
  · rw [root_p2, DodecA.card_conjBy, h.card_X₂']
  · rw [root_p3, DodecA.card_conjBy, h.card_X₁', hq]
  · rw [root_p4, h.card_X₂]
  · rw [root_p5, DodecA.card_conjBy, h.card_X₁, hq]
  · rw [root_p6, DodecA.card_conjBy, h.card_X₂']

theorem Ch6Basics.rootOrdersD4 (h : Ch6Basics D) (hq : D.q₁ = D.q₂ ^ 3) :
    RootOrdersD4 D.root D.q₂ := by
  left
  intro i h1 h6
  interval_cases i
  · rw [root_p1, h.card_X₁, hq]
    simp
  · rw [root_p2, DodecA.card_conjBy, h.card_X₂']
    simp
  · rw [root_p3, DodecA.card_conjBy, h.card_X₁', hq]
    simp
  · rw [root_p4, h.card_X₂]
    simp
  · rw [root_p5, DodecA.card_conjBy, h.card_X₁, hq]
    simp
  · rw [root_p6, DodecA.card_conjBy, h.card_X₂']
    simp

theorem Ch6Basics.act₁ (h : Ch6Basics D) :
    conjBy D.w₁⁻¹ (D.root 1) = D.root (-1) ∧ conjBy D.w₁⁻¹ (D.root (-1)) = D.root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 6 → conjBy D.w₁⁻¹ (D.root i) = D.root (8 - i) ∧
        conjBy D.w₁⁻¹ (D.root (-i)) = D.root (-(8 - i)) := by
  have hX₁ : DodecA.HInv D.H D.X₁ := h.H_norm_X₁
  have hX₁' : DodecA.HInv D.H D.X₁' := h.H_norm_X₁'
  have hX₂ : DodecA.HInv D.H D.X₂ := h.H_norm_X₂
  have hX₂' : DodecA.HInv D.H D.X₂' := h.H_norm_X₂'
  refine ⟨?_, ?_, fun i hi2 hi6 => ?_⟩
  · rw [DodecA.rootk_p1, DodecA.rootk_m1]
    exact DodecA.act₁_gen h hX₁ hX₁' (DodecA.conjBy_w₁_X₁ h) 0 0 (by norm_num)
  · rw [DodecA.rootk_p1, DodecA.rootk_m1]
    exact DodecA.act₁_gen h hX₁' hX₁ (DodecA.conjBy_w₁_X₁' h) 0 0 (by norm_num)
  · interval_cases i
    · rw [show (8 : ℤ) - 2 = 6 by norm_num, DodecA.rootk_p2, DodecA.rootk_p6, DodecA.rootk_m2,
        DodecA.rootk_m6]
      exact ⟨DodecA.act₁_gen h hX₂' hX₂' (DodecA.conjBy_w₁_X₂' h) 2 1 (by norm_num),
        DodecA.act₁_gen h hX₂ hX₂ (DodecA.conjBy_w₁_X₂ h) 2 1 (by norm_num)⟩
    · rw [show (8 : ℤ) - 3 = 5 by norm_num, DodecA.rootk_p3, DodecA.rootk_p5, DodecA.rootk_m3,
        DodecA.rootk_m5]
      exact ⟨DodecA.act₁_gen h hX₁' hX₁ (DodecA.conjBy_w₁_X₁' h) 1 2 (by norm_num),
        DodecA.act₁_gen h hX₁ hX₁' (DodecA.conjBy_w₁_X₁ h) 1 2 (by norm_num)⟩
    · rw [show (8 : ℤ) - 4 = 4 by norm_num, DodecA.rootk_p4, DodecA.rootk_m4]
      exact ⟨DodecA.act₁_gen h hX₂ hX₂ (DodecA.conjBy_w₁_X₂ h) 0 0 (by norm_num),
        DodecA.act₁_gen h hX₂' hX₂' (DodecA.conjBy_w₁_X₂' h) 0 0 (by norm_num)⟩
    · rw [show (8 : ℤ) - 5 = 3 by norm_num, DodecA.rootk_p5, DodecA.rootk_p3, DodecA.rootk_m5,
        DodecA.rootk_m3]
      exact ⟨DodecA.act₁_gen h hX₁ hX₁' (DodecA.conjBy_w₁_X₁ h) 2 1 (by norm_num),
        DodecA.act₁_gen h hX₁' hX₁ (DodecA.conjBy_w₁_X₁' h) 2 1 (by norm_num)⟩
    · rw [show (8 : ℤ) - 6 = 2 by norm_num, DodecA.rootk_p6, DodecA.rootk_p2, DodecA.rootk_m6,
        DodecA.rootk_m2]
      exact ⟨DodecA.act₁_gen h hX₂' hX₂' (DodecA.conjBy_w₁_X₂' h) 1 2 (by norm_num),
        DodecA.act₁_gen h hX₂ hX₂ (DodecA.conjBy_w₁_X₂ h) 1 2 (by norm_num)⟩

theorem Ch6Basics.act₂ (h : Ch6Basics D) :
    conjBy D.r₂⁻¹ (D.root 6) = D.root (-6) ∧ conjBy D.r₂⁻¹ (D.root (-6)) = D.root 6 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 5 → conjBy D.r₂⁻¹ (D.root i) = D.root (6 - i) ∧
        conjBy D.r₂⁻¹ (D.root (-i)) = D.root (-(6 - i)) := by
  have hX₁ : DodecA.HInv D.H D.X₁ := h.H_norm_X₁
  have hX₁' : DodecA.HInv D.H D.X₁' := h.H_norm_X₁'
  have hX₂ : DodecA.HInv D.H D.X₂ := h.H_norm_X₂
  have hX₂' : DodecA.HInv D.H D.X₂' := h.H_norm_X₂'
  refine ⟨?_, ?_, fun i hi1 hi5 => ?_⟩
  · rw [DodecA.rootk_p6, DodecA.rootk_m6]
    exact DodecA.act₂_gen h hX₂' hX₂ (DodecA.conjBy_w₂_X₂' h) 1 1 (by norm_num)
  · rw [DodecA.rootk_p6, DodecA.rootk_m6]
    exact DodecA.act₂_gen h hX₂ hX₂' (DodecA.conjBy_w₂_X₂ h) 1 1 (by norm_num)
  · interval_cases i
    · rw [show (6 : ℤ) - 1 = 5 by norm_num, DodecA.rootk_p1, DodecA.rootk_p5, DodecA.rootk_m1,
        DodecA.rootk_m5]
      exact ⟨DodecA.act₂_gen h hX₁ hX₁ (DodecA.conjBy_w₂_X₁ h) 0 2 (by norm_num),
        DodecA.act₂_gen h hX₁' hX₁' (DodecA.conjBy_w₂_X₁' h) 0 2 (by norm_num)⟩
    · rw [show (6 : ℤ) - 2 = 4 by norm_num, DodecA.rootk_p2, DodecA.rootk_p4, DodecA.rootk_m2,
        DodecA.rootk_m4]
      exact ⟨DodecA.act₂_gen h hX₂' hX₂ (DodecA.conjBy_w₂_X₂' h) 2 0 (by norm_num),
        DodecA.act₂_gen h hX₂ hX₂' (DodecA.conjBy_w₂_X₂ h) 2 0 (by norm_num)⟩
    · rw [show (6 : ℤ) - 3 = 3 by norm_num, DodecA.rootk_p3, DodecA.rootk_m3]
      exact ⟨DodecA.act₂_gen h hX₁' hX₁' (DodecA.conjBy_w₂_X₁' h) 1 1 (by norm_num),
        DodecA.act₂_gen h hX₁ hX₁ (DodecA.conjBy_w₂_X₁ h) 1 1 (by norm_num)⟩
    · rw [show (6 : ℤ) - 4 = 2 by norm_num, DodecA.rootk_p4, DodecA.rootk_p2, DodecA.rootk_m4,
        DodecA.rootk_m2]
      exact ⟨DodecA.act₂_gen h hX₂ hX₂' (DodecA.conjBy_w₂_X₂ h) 0 2 (by norm_num),
        DodecA.act₂_gen h hX₂' hX₂ (DodecA.conjBy_w₂_X₂' h) 0 2 (by norm_num)⟩
    · rw [show (6 : ℤ) - 5 = 1 by norm_num, DodecA.rootk_p5, DodecA.rootk_p1, DodecA.rootk_m5,
        DodecA.rootk_m1]
      exact ⟨DodecA.act₂_gen h hX₁ hX₁ (DodecA.conjBy_w₂_X₁ h) 2 0 (by norm_num),
        DodecA.act₂_gen h hX₁' hX₁' (DodecA.conjBy_w₂_X₁' h) 2 0 (by norm_num)⟩

theorem Ch6Core.opp' (h : Ch6Core D) : D.P ⊓ conjBy ((D.w₁ * D.r₂) ^ 3) D.P = ⊥ := by
  obtain ⟨h', hh', he⟩ := Ch6Basics.cube h.toCh6Basics
  have hP : DodecA.HInv D.H D.P := h.P_normH
  have hw : D.w₁ * D.w₂ ∈ normalizer (D.H : Set G) := mul_mem h.w₁_normH h.w₂_normH
  rw [he, DodecA.conjBy_mul_of_mem hP hw hh']
  exact h.opp

end CFSG.GH74.GLS.Stage4.Rest
