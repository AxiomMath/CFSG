module

public import CFSG.LargeExtraspecial.AS62SemData
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LargeExtraspecial.AS62

structure Frame (G : Type*) [Group G] where
  H : Subgroup G
  V : Subgroup G
  A : Subgroup G
  zz : Fin 5 → G
  V_eq : V = Subgroup.closure (Set.range zz)
  zz_sq : ∀ i, zz i * zz i = 1
  zz_comm : ∀ i j, zz i * zz j = zz j * zz i
  zz_prod : zz 0 * zz 1 * zz 2 * zz 3 * zz 4 = 1
  card_V : Nat.card V = 16
  inf_eq : V ⊓ A = ⊥
  sup_eq : V ⊔ A = H
  σ : A →* Equiv.Perm (Fin 5)
  σ_spec : ∀ (a : A) (i : Fin 5), (a : G) * zz i * (a : G)⁻¹ = zz (σ a i)
  σ_injective : Function.Injective σ
  σ_range : σ.range = alternatingGroup (Fin 5)

namespace Sem

@[expose] def permCode (p : Equiv.Perm (Fin 5)) : ℕ :=
  10000 * (p 0).val + 1000 * (p 1).val + 100 * (p 2).val + 10 * (p 3).val + (p 4).val

theorem app_permCode (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    app (permCode p) i.val = (p i).val := by
  have h0 := (p 0).isLt
  have h1 := (p 1).isLt
  have h2 := (p 2).isLt
  have h3 := (p 3).isLt
  have h4 := (p 4).isLt
  fin_cases i <;> simp only [app, permCode] <;> norm_num <;> omega

theorem permCode_injective : Function.Injective permCode := by
  intro p p' h
  exact Equiv.ext fun i => Fin.ext (by rw [← app_permCode, ← app_permCode, h])

theorem permCode_one : permCode 1 = 1234 := rfl

theorem permCode_eq_sum (p : Equiv.Perm (Fin 5)) :
    permCode p = ∑ i : Fin 5, (p i).val * 10 ^ (4 - i.val) := by
  simp only [permCode, Fin.sum_univ_five]
  norm_num
  ring

theorem app_permCode' (p : Equiv.Perm (Fin 5)) (i : ℕ) (hi : i < 5) :
    app (permCode p) i = (p ⟨i, hi⟩).val :=
  app_permCode p ⟨i, hi⟩

theorem compN_permCode (p p' : Equiv.Perm (Fin 5)) :
    compN (permCode p) (permCode p') = permCode (p * p') := by
  simp only [compN, app_permCode' p' 0 (by decide), app_permCode' p' 1 (by decide),
    app_permCode' p' 2 (by decide), app_permCode' p' 3 (by decide),
    app_permCode' p' 4 (by decide), app_permCode]
  rfl

theorem invN_permCode (p : Equiv.Perm (Fin 5)) : invN (permCode p) = permCode p⁻¹ := by
  have h : invN (permCode p) = ∑ i : Fin 5, i.val * 10 ^ (4 - (p i).val) := by
    simp only [invN, app_permCode' p 0 (by decide), app_permCode' p 1 (by decide),
      app_permCode' p 2 (by decide), app_permCode' p 3 (by decide),
      app_permCode' p 4 (by decide), Fin.sum_univ_five]
    rfl
  rw [h, permCode_eq_sum, ← Equiv.sum_comp p (fun j => (p⁻¹ j).val * 10 ^ (4 - j.val))]
  simp

theorem app_permCode_lt (p : Equiv.Perm (Fin 5)) (i : ℕ) (hi : i < 4) :
    app (permCode p) i < 5 := by
  have := app_permCode p ⟨i, by omega⟩
  simp only at this
  rw [this]
  exact (p _).isLt

theorem lift_mk_cons {α H : Type*} [Group H] (f : α → H) (a : α × Bool) (w : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (a :: w)) =
      cond a.2 (f a.1) (f a.1)⁻¹ * FreeGroup.lift f (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk, List.map_cons, List.prod_cons]

end Sem

open Sem

namespace Frame

variable {G : Type*} [Group G] (F : Frame G)

theorem zz_mem (i : Fin 5) : F.zz i ∈ F.V := by
  rw [F.V_eq]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem V_le_H : F.V ≤ F.H := F.sup_eq ▸ le_sup_left

theorem A_le_H : F.A ≤ F.H := F.sup_eq ▸ le_sup_right

theorem zz_inv (i : Fin 5) : (F.zz i)⁻¹ = F.zz i := inv_eq_of_mul_eq_one_right (F.zz_sq i)

@[expose] def bitPow (g : G) (b : Bool) : G := cond b g 1

@[expose] def vOf (c : ℕ) : G :=
  bitPow (F.zz 0) (c.testBit 0) * (bitPow (F.zz 1) (c.testBit 1) *
    (bitPow (F.zz 2) (c.testBit 2) * bitPow (F.zz 3) (c.testBit 3)))

theorem vOf_zero : F.vOf 0 = 1 := by simp [vOf, bitPow]

theorem commute_zz_bitPow (i j : Fin 5) (b : Bool) : Commute (F.zz i) (bitPow (F.zz j) b) := by
  cases b
  · exact Commute.one_right _
  · exact F.zz_comm i j

theorem zz_mul_bitPow (i : Fin 5) (b : Bool) :
    F.zz i * bitPow (F.zz i) b = bitPow (F.zz i) (!b) := by
  cases b
  · simp [bitPow]
  · simp [bitPow, F.zz_sq]

theorem testBit_xor_two_pow (j d i : ℕ) :
    (2 ^ j ^^^ d).testBit i = (decide (j = i) ^^ d.testBit i) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem zz0_mul_vOf (d : ℕ) : F.zz 0 * F.vOf d = F.vOf (2 ^ 0 ^^^ d) := by
  simp only [vOf, testBit_xor_two_pow]
  simp only [decide_true, Bool.true_xor, show decide (0 = 1) = false from rfl,
    show decide (0 = 2) = false from rfl, show decide (0 = 3) = false from rfl, Bool.false_xor]
  rw [← mul_assoc, F.zz_mul_bitPow]

theorem zz1_mul_vOf (d : ℕ) : F.zz 1 * F.vOf d = F.vOf (2 ^ 1 ^^^ d) := by
  simp only [vOf, testBit_xor_two_pow]
  simp only [decide_true, Bool.true_xor, show decide (1 = 0) = false from rfl,
    show decide (1 = 2) = false from rfl, show decide (1 = 3) = false from rfl, Bool.false_xor]
  rw [(F.commute_zz_bitPow 1 0 _).left_comm, ← mul_assoc (F.zz 1), F.zz_mul_bitPow]

theorem zz2_mul_vOf (d : ℕ) : F.zz 2 * F.vOf d = F.vOf (2 ^ 2 ^^^ d) := by
  simp only [vOf, testBit_xor_two_pow]
  simp only [decide_true, Bool.true_xor, show decide (2 = 0) = false from rfl,
    show decide (2 = 1) = false from rfl, show decide (2 = 3) = false from rfl, Bool.false_xor]
  rw [(F.commute_zz_bitPow 2 0 _).left_comm, (F.commute_zz_bitPow 2 1 _).left_comm,
    ← mul_assoc (F.zz 2), F.zz_mul_bitPow]

theorem zz3_mul_vOf (d : ℕ) : F.zz 3 * F.vOf d = F.vOf (2 ^ 3 ^^^ d) := by
  simp only [vOf, testBit_xor_two_pow]
  simp only [decide_true, Bool.true_xor, show decide (3 = 0) = false from rfl,
    show decide (3 = 1) = false from rfl, show decide (3 = 2) = false from rfl, Bool.false_xor]
  rw [(F.commute_zz_bitPow 3 0 _).left_comm, (F.commute_zz_bitPow 3 1 _).left_comm,
    (F.commute_zz_bitPow 3 2 _).left_comm, F.zz_mul_bitPow]

theorem zz_four : F.zz 4 = F.zz 3 * F.zz 2 * F.zz 1 * F.zz 0 := by
  have h := eq_inv_of_mul_eq_one_right F.zz_prod
  rw [h]
  simp only [mul_inv_rev, F.zz_inv]
  group

theorem zz4_mul_vOf (d : ℕ) : F.zz 4 * F.vOf d = F.vOf (15 ^^^ d) := by
  rw [F.zz_four, mul_assoc, mul_assoc, mul_assoc, F.zz0_mul_vOf, F.zz1_mul_vOf, F.zz2_mul_vOf,
    F.zz3_mul_vOf]
  congr 1
  simp only [← Nat.xor_assoc]
  rfl

theorem zz_mul_vOf (j : Fin 5) (d : ℕ) : F.zz j * F.vOf d = F.vOf (colN j ^^^ d) := by
  fin_cases j
  · exact F.zz0_mul_vOf d
  · exact F.zz1_mul_vOf d
  · exact F.zz2_mul_vOf d
  · exact F.zz3_mul_vOf d
  · exact F.zz4_mul_vOf d

@[expose] def bitN (b : Bool) : ℕ := cond b 1 0

theorem bitPow_mul_vOf (j : Fin 5) (b : Bool) (d : ℕ) :
    bitPow (F.zz j) b * F.vOf d = F.vOf (bitN b * colN j ^^^ d) := by
  cases b
  · simp [bitPow, bitN]
  · simpa [bitPow, bitN] using F.zz_mul_vOf j d

theorem bits_eq : ∀ c, c < 16 → bitN (c.testBit 0) * colN 0 ^^^ bitN (c.testBit 1) * colN 1 ^^^
    bitN (c.testBit 2) * colN 2 ^^^ bitN (c.testBit 3) * colN 3 = c := by
  decide

theorem vOf_mul {c : ℕ} (hc : c < 16) (d : ℕ) : F.vOf c * F.vOf d = F.vOf (c ^^^ d) := by
  conv_lhs => rw [vOf]
  rw [mul_assoc, mul_assoc, mul_assoc, F.bitPow_mul_vOf 3, F.bitPow_mul_vOf 2,
    F.bitPow_mul_vOf 1, F.bitPow_mul_vOf 0]
  congr 1
  simp only [← Nat.xor_assoc]
  rw [show ((0 : Fin 5) : ℕ) = 0 from rfl, show ((1 : Fin 5) : ℕ) = 1 from rfl,
    show ((2 : Fin 5) : ℕ) = 2 from rfl, show ((3 : Fin 5) : ℕ) = 3 from rfl, bits_eq c hc]

theorem vOf_mul_self {c : ℕ} (hc : c < 16) : F.vOf c * F.vOf c = 1 := by
  rw [F.vOf_mul hc, Nat.xor_self, F.vOf_zero]

theorem vOf_inv {c : ℕ} (hc : c < 16) : (F.vOf c)⁻¹ = F.vOf c :=
  inv_eq_of_mul_eq_one_right (F.vOf_mul_self hc)

theorem bitPow_mem (i : Fin 5) (b : Bool) : bitPow (F.zz i) b ∈ F.V := by
  cases b
  · exact F.V.one_mem
  · exact F.zz_mem i

theorem vOf_mem (c : ℕ) : F.vOf c ∈ F.V :=
  F.V.mul_mem (F.bitPow_mem _ _) (F.V.mul_mem (F.bitPow_mem _ _)
    (F.V.mul_mem (F.bitPow_mem _ _) (F.bitPow_mem _ _)))

theorem zz_eq_vOf (i : Fin 5) : F.zz i = F.vOf (colN i) := by
  have h := F.zz_mul_vOf i 0
  rwa [F.vOf_zero, mul_one, Nat.xor_zero] at h

theorem exists_vOf {v : G} (hv : v ∈ F.V) : ∃ c, c < 16 ∧ F.vOf c = v := by
  rw [F.V_eq] at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨colN i, colN_lt i.isLt, (F.zz_eq_vOf i).symm⟩
  | one => exact ⟨0, by decide, F.vOf_zero⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c ^^^ d, xor_lt_16 hc hd, (F.vOf_mul hc d).symm⟩
  | inv x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, hc, (F.vOf_inv hc).symm⟩

theorem vOf_injective {c d : ℕ} (hc : c < 16) (hd : d < 16) (h : F.vOf c = F.vOf d) : c = d := by
  let f : Fin 16 → F.V := fun k => ⟨F.vOf k.val, F.vOf_mem _⟩
  have hsurj : Function.Surjective f := fun v => by
    obtain ⟨c, hc, hv⟩ := F.exists_vOf v.2
    exact ⟨⟨c, hc⟩, Subtype.ext hv⟩
  have hbij := hsurj.bijective_of_nat_card_le (by rw [Nat.card_fin, F.card_V])
  have := hbij.1 (a₁ := ⟨c, hc⟩) (a₂ := ⟨d, hd⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem bitN_testBit (c i : ℕ) : bitN (c.testBit i) = c / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ i) with h | h <;> simp [h, bitN]

theorem conj_vOf (a : F.A) (c : ℕ) :
    (a : G) * F.vOf c * (a : G)⁻¹ = F.vOf (actN (permCode (F.σ a)) c) := by
  have hb : ∀ (i : Fin 5) (b : Bool),
      (a : G) * bitPow (F.zz i) b * (a : G)⁻¹ = bitPow (F.zz (F.σ a i)) b := by
    intro i b
    cases b
    · simp [bitPow]
    · simp [bitPow, F.σ_spec]
  have hm : ∀ g h : G, (a : G) * (g * h) * (a : G)⁻¹ =
      ((a : G) * g * (a : G)⁻¹) * ((a : G) * h * (a : G)⁻¹) := fun g h => by group
  rw [vOf, hm, hm, hm, hb, hb, hb, hb, ← mul_one (bitPow (F.zz (F.σ a 3)) _), ← F.vOf_zero,
    F.bitPow_mul_vOf, F.bitPow_mul_vOf, F.bitPow_mul_vOf, F.bitPow_mul_vOf]
  congr 1
  simp only [actN, Nat.xor_zero, ← Nat.xor_assoc, bitN_testBit]
  rw [app_permCode' _ 0 (by decide), app_permCode' _ 1 (by decide),
    app_permCode' _ 2 (by decide), app_permCode' _ 3 (by decide)]
  norm_num

@[expose] def Rep (h : G) (d : ℕ × ℕ) : Prop :=
  d.1 < 16 ∧ ∃ a : F.A, permCode (F.σ a) = d.2 ∧ h = F.vOf d.1 * a

theorem rep_lt {h : G} {d : ℕ × ℕ} (hd : F.Rep h d) : d.1 < 16 := hd.1

theorem rep_one : F.Rep 1 one :=
  ⟨by decide, 1, by rw [map_one]; rfl, by
    show (1 : G) = F.vOf 0 * ((1 : F.A) : G)
    rw [F.vOf_zero, Subgroup.coe_one, mul_one]⟩

theorem rep_A (a : F.A) : F.Rep a (0, permCode (F.σ a)) :=
  ⟨Nat.zero_lt_succ _, a, rfl, by
    show (a : G) = F.vOf 0 * a
    rw [F.vOf_zero, one_mul]⟩

theorem rep_zz (i : Fin 5) : F.Rep (F.zz i) (colN i, 1234) :=
  ⟨colN_lt i.isLt, 1, by rw [map_one]; rfl, by rw [Subgroup.coe_one, mul_one, F.zz_eq_vOf]⟩

theorem rep_vOf {c : ℕ} (hc : c < 16) : F.Rep (F.vOf c) (c, 1234) :=
  ⟨hc, 1, by rw [map_one]; rfl, by rw [Subgroup.coe_one, mul_one]⟩

theorem rep_mul {h₁ h₂ : G} {d₁ d₂ : ℕ × ℕ} (h1 : F.Rep h₁ d₁) (h2 : F.Rep h₂ d₂) :
    F.Rep (h₁ * h₂) (dmul d₁ d₂) := by
  obtain ⟨c₁, q₁⟩ := d₁
  obtain ⟨c₂, q₂⟩ := d₂
  obtain ⟨hc₁, a₁, rfl, rfl⟩ := h1
  obtain ⟨hc₂, a₂, rfl, rfl⟩ := h2
  have hlt : actN (permCode (F.σ a₁)) c₂ < 16 := actN_lt (app_permCode_lt _) _
  refine ⟨xor_lt_16 hc₁ hlt, a₁ * a₂, by rw [map_mul, ← compN_permCode]; rfl, ?_⟩
  show F.vOf c₁ * a₁ * (F.vOf c₂ * a₂) = F.vOf (c₁ ^^^ actN (permCode (F.σ a₁)) c₂) * ↑(a₁ * a₂)
  rw [← F.vOf_mul hc₁, ← F.conj_vOf, Subgroup.coe_mul]
  group

theorem rep_inv {h : G} {d : ℕ × ℕ} (hd : F.Rep h d) : F.Rep h⁻¹ (dinv d) := by
  obtain ⟨c, q⟩ := d
  obtain ⟨hc, a, rfl, rfl⟩ := hd
  have hq : invN (permCode (F.σ a)) = permCode (F.σ a⁻¹) := by
    rw [map_inv, invN_permCode]
  refine ⟨?_, a⁻¹, hq.symm, ?_⟩
  · show actN (invN (permCode (F.σ a))) c < 16
    rw [hq]
    exact actN_lt (app_permCode_lt _) _
  · show (F.vOf c * a)⁻¹ = F.vOf (actN (invN (permCode (F.σ a))) c) * ↑a⁻¹
    rw [hq, ← F.conj_vOf, Subgroup.coe_inv, inv_inv, mul_inv_rev, F.vOf_inv hc]
    group

theorem rep_congr {h : G} {d d' : ℕ × ℕ} (hd : F.Rep h d) (e : d = d') : F.Rep h d' := e ▸ hd

theorem rep_unique {h : G} {d d' : ℕ × ℕ} (hd : F.Rep h d) (hd' : F.Rep h d') : d = d' := by
  obtain ⟨c, q⟩ := d
  obtain ⟨c', q'⟩ := d'
  obtain ⟨hc, a, rfl, rfl⟩ := hd
  obtain ⟨hc', a', rfl, he⟩ := hd'
  have hx : (F.vOf c')⁻¹ * F.vOf c = (a' : G) * (a : G)⁻¹ := by
    calc (F.vOf c')⁻¹ * F.vOf c = (F.vOf c')⁻¹ * (F.vOf c * a) * (a : G)⁻¹ := by group
      _ = (F.vOf c')⁻¹ * (F.vOf c' * a') * (a : G)⁻¹ := by rw [he]
      _ = (a' : G) * (a : G)⁻¹ := by group
  have hbot : (F.vOf c')⁻¹ * F.vOf c ∈ F.V ⊓ F.A :=
    ⟨F.V.mul_mem (F.V.inv_mem (F.vOf_mem _)) (F.vOf_mem _),
      by rw [hx]; exact F.A.mul_mem a'.2 (F.A.inv_mem a.2)⟩
  rw [F.inf_eq, Subgroup.mem_bot] at hbot
  have hcc : c = c' := F.vOf_injective hc hc' (inv_mul_eq_one.1 hbot).symm
  rw [hbot] at hx
  have haa : a = a' := Subtype.ext (mul_inv_eq_one.1 hx.symm).symm
  rw [hcc, haa]

theorem eq_of_rep {h h' : G} {d : ℕ × ℕ} (hd : F.Rep h d) (hd' : F.Rep h' d) : h = h' := by
  obtain ⟨-, a, ha, rfl⟩ := hd
  obtain ⟨-, a', ha', rfl⟩ := hd'
  rw [F.σ_injective (permCode_injective (ha.trans ha'.symm))]

theorem eq_one_of_rep {h : G} (hd : F.Rep h one) : h = 1 := F.eq_of_rep hd F.rep_one

theorem mem_H_of_rep {h : G} {d : ℕ × ℕ} (hd : F.Rep h d) : h ∈ F.H := by
  obtain ⟨-, a, -, rfl⟩ := hd
  exact F.H.mul_mem (F.V_le_H (F.vOf_mem _)) (F.A_le_H a.2)

theorem rep_exists {h : G} (hh : h ∈ F.H) : ∃ d, F.Rep h d := by
  rw [← F.sup_eq, ← F.V.closure_eq, ← F.A.closure_eq, ← Subgroup.closure_union] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨c, hc, rfl⟩ := F.exists_vOf hx
      exact ⟨_, F.rep_vOf hc⟩
    · exact ⟨_, F.rep_A ⟨x, hx⟩⟩
  | one => exact ⟨_, F.rep_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨_, F.rep_mul hd hd'⟩
  | inv x _ hx =>
    obtain ⟨d, hd⟩ := hx
    exact ⟨_, F.rep_inv hd⟩

theorem rep_lift {n : ℕ} {gens : Fin n → G} {gd : Fin n → ℕ × ℕ}
    (hg : ∀ i, F.Rep (gens i) (gd i)) (w : List (Fin n × Bool)) :
    F.Rep (FreeGroup.lift gens (FreeGroup.mk w)) (semEval gd w) := by
  induction w with
  | nil =>
    rw [show FreeGroup.mk ([] : List (Fin n × Bool)) = 1 from rfl, map_one]
    exact F.rep_one
  | cons a w ih =>
    rw [Sem.lift_mk_cons, semEval_cons]
    obtain ⟨i, b⟩ := a
    cases b
    · exact F.rep_mul (F.rep_inv (hg i)) ih
    · exact F.rep_mul (hg i) ih

theorem lift_eq_one_of_semEval {n : ℕ} {gens : Fin n → G} {gd : Fin n → ℕ × ℕ}
    (hg : ∀ i, F.Rep (gens i) (gd i)) {w : List (Fin n × Bool)} (h : semEval gd w = one) :
    FreeGroup.lift gens (FreeGroup.mk w) = 1 :=
  F.eq_one_of_rep (h ▸ F.rep_lift hg w)

theorem semEval_eq_of_lift_eq {n : ℕ} {gens : Fin n → G} {gd : Fin n → ℕ × ℕ}
    (hg : ∀ i, F.Rep (gens i) (gd i)) {w w' : List (Fin n × Bool)}
    (h : FreeGroup.lift gens (FreeGroup.mk w) = FreeGroup.lift gens (FreeGroup.mk w')) :
    semEval gd w = semEval gd w' :=
  F.rep_unique (F.rep_lift hg w) (h ▸ F.rep_lift hg w')

end Frame

end CFSG.LargeExtraspecial.AS62
