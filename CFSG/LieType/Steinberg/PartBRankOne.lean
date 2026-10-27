module

public import CFSG.LieType.Steinberg.Collection
public import CFSG.LieType.Steinberg.PartB
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

structure RankOneRels (G : Type*) [Group G] (k : Type*) [Field k] where
  x : k → G
  y : k → G
  x_add : ∀ a b, x (a + b) = x a * x b
  y_add : ∀ a b, y (a + b) = y a * y b
  conj_x : ∀ t : k, t ≠ 0 → ∀ a,
    x t * y (-t⁻¹) * x t * x a * (x t * y (-t⁻¹) * x t)⁻¹ = y (-(t ^ 2)⁻¹ * a)

theorem coe_sl2Upper {k : Type*} [Field k] (c : k) :
    ((sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, c; 0, 1] :=
  rfl

theorem coe_sl2Lower {k : Type*} [Field k] (c : k) :
    ((sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; c, 1] :=
  rfl

namespace RankOneRels

variable {G : Type*} [Group G] {k : Type*} [Field k] (R : RankOneRels G k)

@[expose] def w (t : k) : G := R.x t * R.y (-t⁻¹) * R.x t

@[expose] def h (t : k) : G := R.w t * (R.w 1)⁻¹

theorem w_def (t : k) : R.w t = R.x t * R.y (-t⁻¹) * R.x t := rfl

theorem h_def (t : k) : R.h t = R.w t * (R.w 1)⁻¹ := rfl

theorem x_zero : R.x 0 = 1 := by
  have h := R.x_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem y_zero : R.y 0 = 1 := by
  have h := R.y_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem x_neg (a : k) : R.x (-a) = (R.x a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← R.x_add, neg_add_cancel, R.x_zero])

theorem y_neg (a : k) : R.y (-a) = (R.y a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← R.y_add, neg_add_cancel, R.y_zero])

theorem w_inv (t : k) : (R.w t)⁻¹ = R.w (-t) := by
  rw [w_def, w_def, inv_neg, neg_neg, R.x_neg, R.y_neg]
  group

theorem w_conj_x {t : k} (ht : t ≠ 0) (a : k) :
    R.w t * R.x a * (R.w t)⁻¹ = R.y (-(t ^ 2)⁻¹ * a) :=
  R.conj_x t ht a

theorem w_inv_conj_x {t : k} (ht : t ≠ 0) (a : k) :
    (R.w t)⁻¹ * R.x a * R.w t = R.y (-(t ^ 2)⁻¹ * a) := by
  have h := R.w_conj_x (neg_ne_zero.2 ht) a
  rwa [← R.w_inv, inv_inv, neg_sq] at h

theorem w_conj_y {t : k} (ht : t ≠ 0) (a : k) :
    R.w t * R.y a * (R.w t)⁻¹ = R.x (-(t ^ 2) * a) := by
  have h := R.w_inv_conj_x ht (-(t ^ 2) * a)
  rw [show -(t ^ 2)⁻¹ * (-(t ^ 2) * a) = a by field_simp] at h
  rw [← h]
  group

theorem w_inv_conj_y {t : k} (ht : t ≠ 0) (a : k) :
    (R.w t)⁻¹ * R.y a * R.w t = R.x (-(t ^ 2) * a) := by
  have h := R.w_conj_y (neg_ne_zero.2 ht) a
  rwa [← R.w_inv, inv_inv, neg_sq] at h

theorem x_mul_w {t : k} (ht : t ≠ 0) (a : k) :
    R.x a * R.w t = R.w t * R.y (-(t ^ 2)⁻¹ * a) := by
  rw [← R.w_inv_conj_x ht]
  group

theorem y_mul_w {t : k} (ht : t ≠ 0) (a : k) : R.y a * R.w t = R.w t * R.x (-(t ^ 2) * a) := by
  rw [← R.w_inv_conj_y ht]
  group

theorem w_eq_braid {t : k} (ht : t ≠ 0) : R.w t = R.y (-t⁻¹) * R.x t * R.y (-t⁻¹) := by
  have h := R.w_conj_x ht t
  rw [show -(t ^ 2)⁻¹ * t = -t⁻¹ by field_simp] at h
  have h2 := mul_inv_eq_iff_eq_mul.1 h
  apply mul_right_cancel (b := R.x t)
  rw [h2, w_def]
  group

theorem h_one : R.h 1 = 1 := mul_inv_cancel _

theorem w_eq_h_mul (t : k) : R.w t = R.h t * R.w 1 := by
  rw [h_def, inv_mul_cancel_right]

theorem h_conj_x {t : k} (ht : t ≠ 0) (a : k) : R.h t * R.x a * (R.h t)⁻¹ = R.x (t ^ 2 * a) := by
  have e : R.h t * R.x a * (R.h t)⁻¹ = R.w t * ((R.w 1)⁻¹ * R.x a * R.w 1) * (R.w t)⁻¹ := by
    rw [h_def]
    group
  rw [e, R.w_inv_conj_x one_ne_zero, R.w_conj_y ht]
  congr 1
  ring

theorem h_conj_y {t : k} (ht : t ≠ 0) (a : k) :
    R.h t * R.y a * (R.h t)⁻¹ = R.y ((t ^ 2)⁻¹ * a) := by
  have e : R.h t * R.y a * (R.h t)⁻¹ = R.w t * ((R.w 1)⁻¹ * R.y a * R.w 1) * (R.w t)⁻¹ := by
    rw [h_def]
    group
  rw [e, R.w_inv_conj_y one_ne_zero, R.w_conj_x ht]
  congr 1
  ring

theorem h_mul_x {t : k} (ht : t ≠ 0) (a : k) : R.h t * R.x a = R.x (t ^ 2 * a) * R.h t :=
  mul_inv_eq_iff_eq_mul.1 (R.h_conj_x ht a)

theorem h_conj_w {t : k} (ht : t ≠ 0) (u : k) : R.h t * R.w u * (R.h t)⁻¹ = R.w (t ^ 2 * u) := by
  have e : R.h t * R.w u * (R.h t)⁻¹ = (R.h t * R.x u * (R.h t)⁻¹) *
      (R.h t * R.y (-u⁻¹) * (R.h t)⁻¹) * (R.h t * R.x u * (R.h t)⁻¹) := by
    rw [w_def]
    group
  rw [e, R.h_conj_x ht, R.h_conj_y ht, w_def]
  congr 3
  ring

theorem h_conj_h {t : k} (ht : t ≠ 0) (u : k) :
    R.h t * R.h u * (R.h t)⁻¹ = R.h (t ^ 2 * u) * (R.h (t ^ 2))⁻¹ := by
  have e : R.h t * R.h u * (R.h t)⁻¹ =
      (R.h t * R.w u * (R.h t)⁻¹) * (R.h t * R.w 1 * (R.h t)⁻¹)⁻¹ := by
    rw [R.h_def u]
    group
  rw [e, R.h_conj_w ht, R.h_conj_w ht, mul_one, h_def, h_def]
  group

theorem w_mul_w_of_add_eq_one {t u : k} (ht : t ≠ 0) (hu : u ≠ 0) (htu : t + u = 1) :
    R.w (t * u) * R.w (-u) = R.w t * R.w (-1) := by
  have htu0 : t * u ≠ 0 := mul_ne_zero ht hu
  have hu' : -u ≠ 0 := neg_ne_zero.2 hu
  have s1 : R.x (-t) * R.w (t * u) = R.w (t * u) * R.y (t * u ^ 2)⁻¹ := by
    rw [R.x_mul_w htu0]
    congr 2
    field_simp
  have s3 : R.y (-(t * u)⁻¹) * R.y (t * u ^ 2)⁻¹ = R.y (u ^ 2)⁻¹ := by
    rw [← R.y_add]
    congr 1
    field_simp
    linear_combination -htu
  have s4 : R.y (u ^ 2)⁻¹ * R.w (-u) = R.w (-u) * R.x (-1) := by
    rw [R.y_mul_w hu']
    congr 2
    field_simp
  have s5 : R.x (t * u) * R.w (-u) = R.w (-u) * R.y (-(t * u⁻¹)) := by
    rw [R.x_mul_w hu']
    congr 2
    field_simp
  have s7 : R.y (-(t * u)⁻¹) * R.y u⁻¹ = R.y (-t⁻¹) := by
    rw [← R.y_add]
    congr 1
    field_simp
    linear_combination htu
  have s8 : R.y u⁻¹ * R.y (-(t * u⁻¹)) = R.y 1 := by
    rw [← R.y_add]
    congr 1
    field_simp
    linear_combination -htu
  have s9 : R.x (-u) = R.x t * R.x (-1) := by
    rw [← R.x_add]
    congr 1
    linear_combination -htu
  have s6 : R.w (-u) = R.y u⁻¹ * R.x (-u) * R.y u⁻¹ := by
    rw [R.w_eq_braid hu', inv_neg, neg_neg]
  calc R.w (t * u) * R.w (-u)
      = R.x t * (R.x (-t) * R.w (t * u)) * R.w (-u) := by
        rw [← mul_assoc (R.x t), ← R.x_add, add_neg_cancel, R.x_zero, one_mul]
    _ = R.x t * (R.y (-(t * u)⁻¹) * R.x (t * u) * R.y (-(t * u)⁻¹)) * R.y (t * u ^ 2)⁻¹ *
          R.w (-u) := by
        rw [s1, ← R.w_eq_braid htu0]
        group
    _ = R.x t * R.y (-(t * u)⁻¹) * R.x (t * u) *
          (R.y (-(t * u)⁻¹) * R.y (t * u ^ 2)⁻¹) * R.w (-u) := by group
    _ = R.x t * R.y (-(t * u)⁻¹) * (R.x (t * u) * (R.y (u ^ 2)⁻¹ * R.w (-u))) := by
        rw [s3]
        group
    _ = R.x t * R.y (-(t * u)⁻¹) * (R.x (t * u) * R.w (-u)) * R.x (-1) := by
        rw [s4]
        group
    _ = R.x t * R.y (-(t * u)⁻¹) * (R.y u⁻¹ * R.x (-u) * R.y u⁻¹) * R.y (-(t * u⁻¹)) *
          R.x (-1) := by
        rw [s5, s6]
        group
    _ = R.x t * (R.y (-(t * u)⁻¹) * R.y u⁻¹) * R.x (-u) * (R.y u⁻¹ * R.y (-(t * u⁻¹))) *
          R.x (-1) := by group
    _ = R.x t * R.y (-t⁻¹) * R.x t * (R.x (-1) * R.y 1 * R.x (-1)) := by
        rw [s7, s8, s9]
        group
    _ = R.w t * R.w (-1) := by
        rw [R.w_def t, R.w_def (-1), inv_neg, inv_one, neg_neg]

theorem h_mul_of_add_eq_one {t u : k} (ht : t ≠ 0) (hu : u ≠ 0) (htu : t + u = 1) :
    R.h (t * u) = R.h t * R.h u := by
  have e := R.w_mul_w_of_add_eq_one ht hu htu
  rw [← R.w_inv u, ← R.w_inv 1] at e
  rw [h_def, h_def, h_def, mul_inv_eq_iff_eq_mul.1 e]
  group

@[expose] def sub : Subgroup G := Subgroup.closure (Set.range R.x ∪ Set.range R.y)

theorem x_mem_sub (a : k) : R.x a ∈ R.sub := Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)

theorem y_mem_sub (a : k) : R.y a ∈ R.sub := Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)

theorem w_mem_sub (t : k) : R.w t ∈ R.sub :=
  mul_mem (mul_mem (R.x_mem_sub t) (R.y_mem_sub _)) (R.x_mem_sub t)

theorem h_mem_sub (t : k) : R.h t ∈ R.sub := mul_mem (R.w_mem_sub t) (inv_mem (R.w_mem_sub 1))

theorem commute_of_forall {z : G} (hx : ∀ a, z * R.x a * z⁻¹ = R.x a)
    (hy : ∀ a, z * R.y a * z⁻¹ = R.y a) {g : G} (hg : g ∈ R.sub) : Commute z g := by
  have hz : z ∈ Subgroup.centralizer (R.sub : Set G) := by
    rw [sub, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact (mul_inv_eq_iff_eq_mul.1 (hx a)).symm
    · exact (mul_inv_eq_iff_eq_mul.1 (hy a)).symm
  exact (Subgroup.mem_centralizer_iff.1 hz g hg).symm

theorem h_pow_conj_x {v : k} (hv : v ≠ 0) (m : ℕ) (a : k) :
    R.h v ^ m * R.x a * (R.h v ^ m)⁻¹ = R.x ((v ^ 2) ^ m * a) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    calc R.h v ^ (m + 1) * R.x a * (R.h v ^ (m + 1))⁻¹
        = R.h v ^ m * (R.h v * R.x a * (R.h v)⁻¹) * (R.h v ^ m)⁻¹ := by group
      _ = R.x ((v ^ 2) ^ (m + 1) * a) := by
        rw [R.h_conj_x hv, ih]
        congr 1
        ring

theorem h_pow_conj_y {v : k} (hv : v ≠ 0) (m : ℕ) (a : k) :
    R.h v ^ m * R.y a * (R.h v ^ m)⁻¹ = R.y (((v ^ 2) ^ m)⁻¹ * a) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    calc R.h v ^ (m + 1) * R.y a * (R.h v ^ (m + 1))⁻¹
        = R.h v ^ m * (R.h v * R.y a * (R.h v)⁻¹) * (R.h v ^ m)⁻¹ := by group
      _ = R.y (((v ^ 2) ^ (m + 1))⁻¹ * a) := by
        rw [R.h_conj_y hv, ih]
        congr 1
        ring

theorem commute_h_pow_inv_mul {v : k} (hv : v ≠ 0) (m : ℕ) {g : G} (hg : g ∈ R.sub) :
    Commute ((R.h v ^ m)⁻¹ * R.h (v ^ m)) g := by
  have hvm : v ^ m ≠ 0 := pow_ne_zero m hv
  refine R.commute_of_forall (fun a => ?_) (fun a => ?_) hg
  · have e := R.h_pow_conj_x hv m a
    calc (R.h v ^ m)⁻¹ * R.h (v ^ m) * R.x a * ((R.h v ^ m)⁻¹ * R.h (v ^ m))⁻¹
        = (R.h v ^ m)⁻¹ * (R.h (v ^ m) * R.x a * (R.h (v ^ m))⁻¹) * R.h v ^ m := by group
      _ = (R.h v ^ m)⁻¹ * (R.h v ^ m * R.x a * (R.h v ^ m)⁻¹) * R.h v ^ m := by
        rw [R.h_conj_x hvm, e, ← pow_mul, ← pow_mul, mul_comm m 2]
      _ = R.x a := by group
  · have e := R.h_pow_conj_y hv m a
    calc (R.h v ^ m)⁻¹ * R.h (v ^ m) * R.y a * ((R.h v ^ m)⁻¹ * R.h (v ^ m))⁻¹
        = (R.h v ^ m)⁻¹ * (R.h (v ^ m) * R.y a * (R.h (v ^ m))⁻¹) * R.h v ^ m := by group
      _ = (R.h v ^ m)⁻¹ * (R.h v ^ m * R.y a * (R.h v ^ m)⁻¹) * R.h v ^ m := by
        rw [R.h_conj_y hvm, e, ← pow_mul, ← pow_mul, mul_comm m 2]
      _ = R.y a := by group

theorem commute_h [Finite k] {t u : k} (ht : t ≠ 0) (hu : u ≠ 0) : Commute (R.h t) (R.h u) := by
  obtain ⟨v, hv⟩ := IsCyclic.exists_monoid_generator (α := kˣ)
  obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hv (Units.mk0 t ht))
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hv (Units.mk0 u hu))
  have hv0 : (v : k) ≠ 0 := v.ne_zero
  have htm : t = (v : k) ^ m := by rw [← Units.val_pow_eq_pow_val, hm, Units.val_mk0]
  have hun : u = (v : k) ^ n := by rw [← Units.val_pow_eq_pow_val, hn, Units.val_mk0]
  have hdec : ∀ j : ℕ, R.h ((v : k) ^ j) = R.h v ^ j * ((R.h v ^ j)⁻¹ * R.h ((v : k) ^ j)) :=
    fun j => by rw [mul_inv_cancel_left]
  have hmem : ∀ j : ℕ, (R.h v ^ j)⁻¹ * R.h ((v : k) ^ j) ∈ R.sub :=
    fun j => mul_mem (inv_mem (pow_mem (R.h_mem_sub _) j)) (R.h_mem_sub _)
  rw [htm, hun, hdec m, hdec n]
  refine Commute.mul_left (Commute.mul_right (Commute.pow_pow_self _ m n) ?_)
    (Commute.mul_right ?_ (R.commute_h_pow_inv_mul hv0 m (hmem n)))
  · exact (R.commute_h_pow_inv_mul hv0 n (pow_mem (R.h_mem_sub _) m)).symm
  · exact R.commute_h_pow_inv_mul hv0 m (pow_mem (R.h_mem_sub _) n)

theorem h_sq_mul [Finite k] {r t : k} (hr : r ≠ 0) (ht : t ≠ 0) :
    R.h (r ^ 2 * t) = R.h (r ^ 2) * R.h t := by
  have e := R.h_conj_h hr t
  rw [(R.commute_h hr ht).eq, mul_inv_cancel_right] at e
  rw [← eq_mul_inv_iff_mul_eq.1 e, (R.commute_h ht (pow_ne_zero 2 hr)).eq]

end RankOneRels

section Squares

variable {k : Type*} [Field k] [Fintype k]

theorem exists_sq_mul_of_not_isSquare (hk : ringChar k ≠ 2) {s t : k} (hs : ¬IsSquare s)
    (ht : ¬IsSquare t) : ∃ r, r ≠ 0 ∧ s = r ^ 2 * t := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ IsSquare.zero)
  have ht0 : t ≠ 0 := fun h => ht (h ▸ IsSquare.zero)
  have hneg : ∀ {a : k}, a ≠ 0 → ¬IsSquare a → a ^ (Fintype.card k / 2) = -1 := fun ha ha' =>
    (FiniteField.pow_dichotomy hk ha).resolve_left fun h1 =>
      ha' ((FiniteField.isSquare_iff hk ha).2 h1)
  have hsq : IsSquare (s * t⁻¹) := by
    rw [FiniteField.isSquare_iff hk (mul_ne_zero hs0 (inv_ne_zero ht0)), mul_pow, inv_pow,
      hneg hs0 hs, hneg ht0 ht, inv_neg, inv_one, neg_mul_neg, mul_one]
  obtain ⟨r, hr⟩ := hsq
  refine ⟨r, fun h => mul_ne_zero hs0 (inv_ne_zero ht0) (by rw [hr, h, mul_zero]), ?_⟩
  rw [sq, ← hr, mul_assoc, inv_mul_cancel₀ ht0, mul_one]

theorem exists_not_isSquare_add_eq_one (hk : ringChar k ≠ 2) :
    ∃ t u : k, ¬IsSquare t ∧ ¬IsSquare u ∧ t + u = 1 := by
  classical
  by_contra H
  push Not at H
  have H' : ∀ t : k, ¬IsSquare t → IsSquare (1 - t) := fun t ht => by
    by_contra h
    exact H t (1 - t) ht h (by ring)
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hk
  have hn0 : n ≠ 0 := fun h => hn (h ▸ IsSquare.zero)
  set Q := Finset.univ.filter (fun s : k => s ≠ 0 ∧ IsSquare s)
  set N := Finset.univ.filter (fun s : k => ¬IsSquare s)
  have h1 : Q.card ≤ N.card := by
    refine Finset.card_le_card_of_injOn (n * ·) (fun s hs => ?_)
      (fun a _ b _ hab => mul_left_cancel₀ hn0 hab)
    simp only [Q, N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    obtain ⟨hs0, a, rfl⟩ := hs
    rintro ⟨r, hr⟩
    have ha : a ≠ 0 := fun h => hs0 (by rw [h, mul_zero])
    exact hn ⟨r / a, by field_simp; linear_combination hr⟩
  have h2 : N.card ≤ (Q.erase 1).card := by
    refine Finset.card_le_card_of_injOn (1 - ·) (fun t ht => ?_)
      (fun a _ b _ hab => sub_right_injective hab)
    simp only [Q, N, Finset.coe_filter, Finset.coe_erase, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff] at ht ⊢
    refine ⟨⟨fun h => ht ?_, H' t ht⟩, fun h => ht ?_⟩
    · rw [← sub_eq_zero.1 h]
      exact IsSquare.one
    · rw [show t = 0 by linear_combination -h]
      exact IsSquare.zero
  have h3 : 1 ∈ Q := by simp [Q]
  rw [Finset.card_erase_of_mem h3] at h2
  have := Finset.card_pos.2 ⟨1, h3⟩
  omega

end Squares

namespace RankOneRels

variable {G : Type*} [Group G] {k : Type*} [Field k] (R : RankOneRels G k)

theorem h_mul [Finite k] {s t : k} (hs : s ≠ 0) (ht : t ≠ 0) : R.h (s * t) = R.h s * R.h t := by
  have : Fintype k := Fintype.ofFinite k
  by_cases hsq : IsSquare s
  · obtain ⟨r, rfl⟩ := hsq
    have hr : r ≠ 0 := fun h => hs (by rw [h, mul_zero])
    rw [← sq]
    exact R.h_sq_mul hr ht
  by_cases htq : IsSquare t
  · obtain ⟨r, rfl⟩ := htq
    have hr : r ≠ 0 := fun h => ht (by rw [h, mul_zero])
    rw [mul_comm, ← sq, R.h_sq_mul hr hs, (R.commute_h (pow_ne_zero 2 hr) hs).eq]
  have hk : ringChar k ≠ 2 := fun h2 => hsq (FiniteField.isSquare_of_char_two h2 s)
  obtain ⟨t₁, u₁, h1, h2, h12⟩ := exists_not_isSquare_add_eq_one hk
  have ht₁ : t₁ ≠ 0 := fun h => h1 (h ▸ IsSquare.zero)
  have hu₁ : u₁ ≠ 0 := fun h => h2 (h ▸ IsSquare.zero)
  obtain ⟨r, hr, rfl⟩ := exists_sq_mul_of_not_isSquare hk hsq h1
  obtain ⟨q, hq, rfl⟩ := exists_sq_mul_of_not_isSquare hk htq h2
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  calc R.h (r ^ 2 * t₁ * (q ^ 2 * u₁)) = R.h (r ^ 2 * (q ^ 2 * (t₁ * u₁))) := by ring_nf
    _ = R.h (r ^ 2) * (R.h (q ^ 2) * (R.h t₁ * R.h u₁)) := by
        rw [R.h_sq_mul hr (mul_ne_zero hq2 (mul_ne_zero ht₁ hu₁)),
          R.h_sq_mul hq (mul_ne_zero ht₁ hu₁), R.h_mul_of_add_eq_one ht₁ hu₁ h12]
    _ = R.h (r ^ 2) * R.h t₁ * (R.h (q ^ 2) * R.h u₁) := by
        rw [← mul_assoc (R.h (q ^ 2)), (R.commute_h hq2 ht₁).eq]
        group
    _ = R.h (r ^ 2 * t₁) * R.h (q ^ 2 * u₁) := by
        rw [R.h_sq_mul hr ht₁, R.h_sq_mul hq hu₁]

@[expose] def bruhat : Set G :=
  {g | (∃ a t, t ≠ 0 ∧ g = R.x a * R.h t) ∨ ∃ a b t, t ≠ 0 ∧ g = R.x a * R.w 1 * R.x b * R.h t}

theorem one_mem_bruhat : (1 : G) ∈ R.bruhat :=
  Or.inl ⟨0, 1, one_ne_zero, by rw [R.x_zero, R.h_one, one_mul]⟩

theorem y_eq_conj (a : k) : R.y a = R.w 1 * R.x (-a) * (R.w 1)⁻¹ := by
  rw [R.w_conj_x one_ne_zero]
  congr 1
  ring

section Bruhat

variable (hC : ∀ s t : k, s ≠ 0 → t ≠ 0 → R.h (s * t) = R.h s * R.h t)
include hC

theorem h_inv {t : k} (ht : t ≠ 0) : (R.h t)⁻¹ = R.h t⁻¹ :=
  (eq_inv_of_mul_eq_one_left (by rw [← hC _ _ (inv_ne_zero ht) ht, inv_mul_cancel₀ ht,
    R.h_one])).symm

theorem w_one_mul_h {t : k} (ht : t ≠ 0) : R.w 1 * R.h t = R.h t⁻¹ * R.w 1 := by
  have e := R.h_conj_w ht 1
  rw [mul_one, R.w_eq_h_mul (t ^ 2)] at e
  have e2 : R.h t * R.w 1 = R.h (t ^ 2) * R.w 1 * R.h t := mul_inv_eq_iff_eq_mul.1 e
  calc R.w 1 * R.h t = (R.h (t ^ 2))⁻¹ * (R.h (t ^ 2) * R.w 1 * R.h t) := by group
    _ = (R.h (t ^ 2))⁻¹ * (R.h t * R.w 1) := by rw [← e2]
    _ = R.h ((t ^ 2)⁻¹ * t) * R.w 1 := by
        rw [R.h_inv hC (pow_ne_zero 2 ht), hC _ _ (inv_ne_zero (pow_ne_zero 2 ht)) ht]
        group
    _ = R.h t⁻¹ * R.w 1 := by
        congr 2
        field_simp

theorem h_mul_w_one {t : k} (ht : t ≠ 0) : R.h t * R.w 1 = R.w 1 * R.h t⁻¹ := by
  rw [R.w_one_mul_h hC (inv_ne_zero ht), inv_inv]

theorem w_one_mul_w_one : R.w 1 * R.w 1 = R.h (-1) := by
  have e : (R.w 1)⁻¹ = R.h (-1) * R.w 1 := by rw [R.w_inv, R.w_eq_h_mul]
  have e2 : R.h (-1) = (R.w 1)⁻¹ * (R.w 1)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, ← e]
  rw [← inv_inv (R.w 1 * R.w 1), mul_inv_rev, ← e2, R.h_inv hC (neg_ne_zero.2 one_ne_zero),
    inv_neg, inv_one]

theorem w_one_mul_x_mul_w_one {b : k} (hb : b ≠ 0) :
    R.w 1 * R.x b * R.w 1 = R.x (-b⁻¹) * R.w 1 * R.x (-b) * R.h (-b) := by
  have e1 : R.y (-b) = R.x (-b⁻¹) * R.w b⁻¹ * R.x (-b⁻¹) := by
    rw [R.w_def, inv_inv, R.x_neg]
    group
  calc R.w 1 * R.x b * R.w 1 = (R.w 1 * R.x b * (R.w 1)⁻¹) * (R.w 1 * R.w 1) := by group
    _ = R.y (-b) * R.h (-1) := by
        rw [R.w_conj_x one_ne_zero, R.w_one_mul_w_one hC]
        congr 2
        ring
    _ = R.x (-b⁻¹) * (R.h b⁻¹ * R.w 1) * R.x (-b⁻¹) * R.h (-1) := by
        rw [e1, R.w_eq_h_mul]
    _ = R.x (-b⁻¹) * R.w 1 * (R.h b * R.x (-b⁻¹)) * R.h (-1) := by
        rw [← R.w_one_mul_h hC hb]
        group
    _ = R.x (-b⁻¹) * R.w 1 * R.x (b ^ 2 * -b⁻¹) * R.h (b * -1) := by
        rw [R.h_mul_x hb, hC _ _ hb (neg_ne_zero.2 one_ne_zero)]
        group
    _ = R.x (-b⁻¹) * R.w 1 * R.x (-b) * R.h (-b) := by
        rw [mul_neg_one, show b ^ 2 * -b⁻¹ = -b by field_simp]

omit hC in
theorem mul_x_mem_bruhat {g : G} (hg : g ∈ R.bruhat) (c : k) : g * R.x c ∈ R.bruhat := by
  rcases hg with ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · refine Or.inl ⟨a + t ^ 2 * c, t, ht, ?_⟩
    rw [mul_assoc _ (R.h t), R.h_mul_x ht, R.x_add]
    group
  · refine Or.inr ⟨a, b + t ^ 2 * c, t, ht, ?_⟩
    rw [mul_assoc _ (R.h t), R.h_mul_x ht, R.x_add b]
    group

theorem mul_h_mem_bruhat {g : G} (hg : g ∈ R.bruhat) {s : k} (hs : s ≠ 0) :
    g * R.h s ∈ R.bruhat := by
  rcases hg with ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · exact Or.inl ⟨a, t * s, mul_ne_zero ht hs, by rw [hC _ _ ht hs, mul_assoc]⟩
  · exact Or.inr ⟨a, b, t * s, mul_ne_zero ht hs, by rw [hC _ _ ht hs, mul_assoc]⟩

theorem mul_w_mem_bruhat {g : G} (hg : g ∈ R.bruhat) : g * R.w 1 ∈ R.bruhat := by
  rcases hg with ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · refine Or.inr ⟨a, 0, t⁻¹, inv_ne_zero ht, ?_⟩
    rw [R.x_zero, mul_one, mul_assoc, R.h_mul_w_one hC ht, ← mul_assoc]
  by_cases hb : b = 0
  · refine Or.inl ⟨a, -t⁻¹, neg_ne_zero.2 (inv_ne_zero ht), ?_⟩
    calc R.x a * R.w 1 * R.x b * R.h t * R.w 1 = R.x a * (R.w 1 * R.w 1) * R.h t⁻¹ := by
          rw [hb, R.x_zero, mul_assoc _ (R.h t), R.h_mul_w_one hC ht]
          group
      _ = R.x a * R.h (-t⁻¹) := by
          rw [R.w_one_mul_w_one hC, mul_assoc,
            ← hC _ _ (neg_ne_zero.2 one_ne_zero) (inv_ne_zero ht), neg_one_mul]
  · refine Or.inr ⟨a - b⁻¹, -b, -b * t⁻¹, mul_ne_zero (neg_ne_zero.2 hb) (inv_ne_zero ht), ?_⟩
    calc R.x a * R.w 1 * R.x b * R.h t * R.w 1 = R.x a * (R.w 1 * R.x b * R.w 1) * R.h t⁻¹ := by
          rw [mul_assoc _ (R.h t), R.h_mul_w_one hC ht]
          group
      _ = R.x a * R.x (-b⁻¹) * R.w 1 * R.x (-b) * (R.h (-b) * R.h t⁻¹) := by
          rw [R.w_one_mul_x_mul_w_one hC hb]
          group
      _ = R.x (a - b⁻¹) * R.w 1 * R.x (-b) * R.h (-b * t⁻¹) := by
          rw [← hC _ _ (neg_ne_zero.2 hb) (inv_ne_zero ht), sub_eq_add_neg, R.x_add]

theorem mul_w_inv_mem_bruhat {g : G} (hg : g ∈ R.bruhat) : g * (R.w 1)⁻¹ ∈ R.bruhat := by
  rw [R.w_inv, R.w_eq_h_mul, ← mul_assoc]
  exact R.mul_w_mem_bruhat hC (R.mul_h_mem_bruhat hC hg (neg_ne_zero.2 one_ne_zero))

theorem mul_y_mem_bruhat {g : G} (hg : g ∈ R.bruhat) (c : k) : g * R.y c ∈ R.bruhat := by
  rw [R.y_eq_conj c, ← mul_assoc, ← mul_assoc]
  exact R.mul_w_inv_mem_bruhat hC (R.mul_x_mem_bruhat (R.mul_w_mem_bruhat hC hg) _)

theorem sub_subset_bruhat {g : G} (hg : g ∈ R.sub) : g ∈ R.bruhat := by
  refine Subgroup.closure_induction_right (p := fun g _ => g ∈ R.bruhat) R.one_mem_bruhat
    (fun g _ z hz ih => ?_) (fun g _ z hz ih => ?_) hg
  · rcases hz with ⟨c, rfl⟩ | ⟨c, rfl⟩
    exacts [R.mul_x_mem_bruhat ih c, R.mul_y_mem_bruhat hC ih c]
  · rcases hz with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [← R.x_neg]
      exact R.mul_x_mem_bruhat ih _
    · rw [← R.y_neg]
      exact R.mul_y_mem_bruhat hC ih _

end Bruhat

section Kernel

variable {K : Type*} [Group K] (ρ : G →* K) (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K)

theorem map_w (hρx : ∀ a, ρ (R.x a) = φ (sl2Upper a)) (hρy : ∀ a, ρ (R.y a) = φ (sl2Lower a))
    (t : k) : ρ (R.w t) = φ (sl2Upper t * sl2Lower (-t⁻¹) * sl2Upper t) := by
  rw [R.w_def, map_mul, map_mul, map_mul, map_mul, hρx, hρy]

theorem eq_one_of_mem_bruhat (hφ : Function.Injective φ)
    (hρx : ∀ a, ρ (R.x a) = φ (sl2Upper a)) (hρy : ∀ a, ρ (R.y a) = φ (sl2Lower a)) {g : G}
    (hg : g ∈ R.bruhat) (h1 : ρ g = 1) : g = 1 := by
  have hw := R.map_w ρ φ hρx hρy
  rcases hg with ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · have e : sl2Upper a * (sl2Upper t * sl2Lower (-t⁻¹) * sl2Upper t) =
        sl2Upper 1 * sl2Lower (-1⁻¹) * sl2Upper 1 := by
      apply hφ
      rw [R.h_def, ← mul_assoc, map_mul, map_inv, mul_inv_eq_one, map_mul, hρx, hw, hw] at h1
      rw [map_mul, h1]
    have e01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 1) e
    have e00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 0) e
    simp [coe_sl2Upper, coe_sl2Lower, mul_inv_cancel₀ ht, inv_mul_cancel₀ ht] at e01 e00
    rw [e00.resolve_right ht, e01, R.x_zero, R.h_one, mul_one]
  · exfalso
    have e : sl2Upper a * (sl2Upper 1 * sl2Lower (-1⁻¹) * sl2Upper 1) * sl2Upper b *
        (sl2Upper t * sl2Lower (-t⁻¹) * sl2Upper t) =
        sl2Upper 1 * sl2Lower (-1⁻¹) * sl2Upper 1 := by
      apply hφ
      rw [R.h_def, ← mul_assoc, map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, map_mul,
        hρx, hρx, hw, hw] at h1
      rw [map_mul, map_mul, map_mul, h1]
    have e11 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 1 1) e
    simp [coe_sl2Upper, coe_sl2Lower, mul_inv_cancel₀ ht, inv_mul_cancel₀ ht] at e11
    exact ht e11

theorem eq_one_of_map_eq_one [Finite k] (hφ : Function.Injective φ)
    (hρx : ∀ a, ρ (R.x a) = φ (sl2Upper a)) (hρy : ∀ a, ρ (R.y a) = φ (sl2Lower a)) {g : G}
    (hg : g ∈ R.sub) (h1 : ρ g = 1) : g = 1 :=
  R.eq_one_of_mem_bruhat ρ φ hφ hρx hρy
    (R.sub_subset_bruhat (fun _ _ hs ht => R.h_mul hs ht) hg) h1

theorem injOn_sub [Finite k] (hφ : Function.Injective φ)
    (hρx : ∀ a, ρ (R.x a) = φ (sl2Upper a)) (hρy : ∀ a, ρ (R.y a) = φ (sl2Lower a)) :
    Set.InjOn ρ R.sub :=
  injOn_of_eq_one fun _ hg h1 => R.eq_one_of_map_eq_one ρ φ hφ hρx hρy hg h1

end Kernel

end RankOneRels

end CFSG.LieType.Steinberg
