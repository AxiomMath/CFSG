module

public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GH74.GLS.SP.Local.SL2Root

open Subgroup CFSG.GH74.GLS.IVK.L2Torus CFSG.SL2MinimalFaithful

@[expose] def upperSub (F : Type*) [Field F] : Subgroup (SL2m F) where
  carrier := {x | x.1 0 0 = 1 ∧ x.1 1 1 = 1 ∧ x.1 1 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply', hx0, hx1, hx2, hy0, hy1, hy2]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx0, hx1, hx2⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [inv_apply_00, inv_apply_10, inv_apply_11, hx0, hx1, hx2]

@[expose] def lowerSub (F : Type*) [Field F] : Subgroup (SL2m F) where
  carrier := {x | x.1 0 0 = 1 ∧ x.1 1 1 = 1 ∧ x.1 0 1 = 0}
  mul_mem' := by
    rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply', hx0, hx1, hx2, hy0, hy1, hy2]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx0, hx1, hx2⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [inv_apply_00, inv_apply_01, inv_apply_11, hx0, hx1, hx2]

variable {F : Type*} [Field F]

theorem mem_upperSub {x : SL2m F} :
    x ∈ upperSub F ↔ x.1 0 0 = 1 ∧ x.1 1 1 = 1 ∧ x.1 1 0 = 0 := Iff.rfl

theorem mem_lowerSub {x : SL2m F} :
    x ∈ lowerSub F ↔ x.1 0 0 = 1 ∧ x.1 1 1 = 1 ∧ x.1 0 1 = 0 := Iff.rfl

@[expose] def lMat (s : F) : SL2m F := sl2 1 0 s 1 (by ring)

@[simp] theorem unipotent_00 (s : F) : (unipotent s : SL2m F).1 0 0 = 1 := by
  simp [coe_unipotent]

@[simp] theorem unipotent_01 (s : F) : (unipotent s : SL2m F).1 0 1 = s := by
  simp [coe_unipotent]

@[simp] theorem unipotent_10 (s : F) : (unipotent s : SL2m F).1 1 0 = 0 := by
  simp [coe_unipotent]

@[simp] theorem unipotent_11 (s : F) : (unipotent s : SL2m F).1 1 1 = 1 := by
  simp [coe_unipotent]

@[simp] theorem lMat_00 (s : F) : (lMat s).1 0 0 = 1 := by simp [lMat]

@[simp] theorem lMat_01 (s : F) : (lMat s).1 0 1 = 0 := by simp [lMat]

@[simp] theorem lMat_10 (s : F) : (lMat s).1 1 0 = s := by simp [lMat]

@[simp] theorem lMat_11 (s : F) : (lMat s).1 1 1 = 1 := by simp [lMat]

theorem unipotent_mem_upperSub (s : F) : unipotent s ∈ upperSub F := by
  simp [mem_upperSub]

theorem lMat_mem_lowerSub (s : F) : lMat s ∈ lowerSub F := by
  simp [mem_lowerSub]

theorem eq_unipotent_of_mem_upperSub {x : SL2m F} (hx : x ∈ upperSub F) :
    x = unipotent (x.1 0 1) := by
  obtain ⟨h0, h1, h2⟩ := hx
  apply sl2_ext <;> simp [h0, h1, h2]

theorem eq_lMat_of_mem_lowerSub {x : SL2m F} (hx : x ∈ lowerSub F) :
    x = lMat (x.1 1 0) := by
  obtain ⟨h0, h1, h2⟩ := hx
  apply sl2_ext <;> simp [h0, h1, h2]

theorem card_upperSub : Nat.card (upperSub F) = Nat.card F := by
  symm
  refine Nat.card_congr
    { toFun := fun s => ⟨unipotent s, unipotent_mem_upperSub s⟩
      invFun := fun x => x.1.1 0 1
      left_inv := fun s => by simp
      right_inv := fun x => by
        apply Subtype.ext
        exact (eq_unipotent_of_mem_upperSub x.2).symm }

theorem card_lowerSub : Nat.card (lowerSub F) = Nat.card F := by
  symm
  refine Nat.card_congr
    { toFun := fun s => ⟨lMat s, lMat_mem_lowerSub s⟩
      invFun := fun x => x.1.1 1 0
      left_inv := fun s => by simp
      right_inv := fun x => by
        apply Subtype.ext
        exact (eq_lMat_of_mem_lowerSub x.2).symm }

theorem upperSub_comm {x y : SL2m F} (hx : x ∈ upperSub F) (hy : y ∈ upperSub F) :
    x * y = y * x := by
  rw [eq_unipotent_of_mem_upperSub hx, eq_unipotent_of_mem_upperSub hy, ← unipotent_add,
    ← unipotent_add, add_comm]

theorem unipotent_pow (s : F) (n : ℕ) : (unipotent s : SL2m F) ^ n = unipotent (n • s) := by
  induction n with
  | zero => simp [unipotent_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, unipotent_add]

theorem upperSub_pow_char {p : ℕ} [CharP F p] {x : SL2m F} (hx : x ∈ upperSub F) :
    x ^ p = 1 := by
  rw [eq_unipotent_of_mem_upperSub hx, unipotent_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    unipotent_zero]

theorem diag_conj_00 {d : SL2m F} (hd : d ∈ diagSub F) (M : SL2m F) :
    (d * M * d⁻¹).1 0 0 = M.1 0 0 := by
  obtain ⟨h1, h2⟩ := hd
  have hdet := sl2_det d
  rw [h1, h2] at hdet
  simp only [mul_apply', inv_apply_00, inv_apply_10, h1, h2]
  linear_combination M.1 0 0 * hdet

theorem diag_conj_11 {d : SL2m F} (hd : d ∈ diagSub F) (M : SL2m F) :
    (d * M * d⁻¹).1 1 1 = M.1 1 1 := by
  obtain ⟨h1, h2⟩ := hd
  have hdet := sl2_det d
  rw [h1, h2] at hdet
  simp only [mul_apply', inv_apply_01, inv_apply_11, h1, h2]
  linear_combination M.1 1 1 * hdet

theorem diag_conj_01 {d : SL2m F} (hd : d ∈ diagSub F) (M : SL2m F) :
    (d * M * d⁻¹).1 0 1 = d.1 0 0 * d.1 0 0 * M.1 0 1 := by
  have h1 := hd.1
  simp only [mul_apply', inv_apply_01, inv_apply_11, h1]
  ring

theorem diag_conj_10 {d : SL2m F} (hd : d ∈ diagSub F) (M : SL2m F) :
    (d * M * d⁻¹).1 1 0 = d.1 1 1 * d.1 1 1 * M.1 1 0 := by
  have h2 := hd.2
  simp only [mul_apply', inv_apply_00, inv_apply_10, h2]
  ring

theorem diag_conj_mem_upperSub {d : SL2m F} (hd : d ∈ diagSub F) {x : SL2m F}
    (hx : x ∈ upperSub F) : d * x * d⁻¹ ∈ upperSub F := by
  obtain ⟨h0, h1, h2⟩ := hx
  exact ⟨by rw [diag_conj_00 hd, h0], by rw [diag_conj_11 hd, h1],
    by rw [diag_conj_10 hd, h2, mul_zero]⟩

theorem diag_conj_mem_upperSub_iff {d : SL2m F} (hd : d ∈ diagSub F) (x : SL2m F) :
    d * x * d⁻¹ ∈ upperSub F ↔ x ∈ upperSub F := by
  refine ⟨fun h => ?_, diag_conj_mem_upperSub hd⟩
  have := diag_conj_mem_upperSub ((diagSub F).inv_mem hd) h
  simpa [mul_assoc] using this

theorem diag_comm {x y : SL2m F} (hx : x ∈ diagSub F) (hy : y ∈ diagSub F) : x * y = y * x := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  apply sl2_ext
  all_goals simp [mul_apply', hx1, hx2, hy1, hy2, mul_comm]

theorem sq_ne_one_of_orderOf {τ : SL2m F} (hτ : τ ∈ diagSub F) (h : 2 < orderOf τ) :
    τ.1 0 0 * τ.1 0 0 ≠ 1 := by
  intro h1
  obtain ⟨ht1, ht2⟩ := hτ
  have hdet := sl2_det τ
  rw [ht1, ht2] at hdet
  have h3 : τ.1 1 1 = τ.1 0 0 := by linear_combination τ.1 0 0 * hdet - τ.1 1 1 * h1
  have h2 : τ ^ 2 = 1 := by
    rw [pow_two]
    apply sl2_ext <;> simp [mul_apply', ht1, ht2, h3, h1]
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  omega

theorem mem_lowerSub_iff_w0 (x : SL2m F) :
    x ∈ lowerSub F ↔ w0 F * x * (w0 F)⁻¹ ∈ upperSub F := by
  simp only [mem_upperSub, mem_lowerSub, mul_apply', inv_apply_00, inv_apply_01, inv_apply_10,
    inv_apply_11, w0, sl2_val]
  simp
  tauto

theorem upperSub_ne_lowerSub : upperSub F ≠ lowerSub F := by
  intro h
  have : (unipotent (1 : F) : SL2m F) ∈ lowerSub F := h ▸ unipotent_mem_upperSub 1
  have h1 := this.2.2
  simp at h1

theorem upperSub_sup_lowerSub : upperSub F ⊔ lowerSub F = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hU : ∀ t, unipotent t ∈ upperSub F ⊔ lowerSub F := fun t =>
    Subgroup.mem_sup_left (unipotent_mem_upperSub t)
  have hL : ∀ t, lMat t ∈ upperSub F ⊔ lowerSub F := fun t =>
    Subgroup.mem_sup_right (lMat_mem_lowerSub t)
  have key : ∀ y : SL2m F, y.1 1 0 ≠ 0 → y ∈ upperSub F ⊔ lowerSub F := by
    intro y hc
    have hdet := sl2_det y
    have hy : y = unipotent ((y.1 0 0 - 1) / y.1 1 0) * lMat (y.1 1 0) *
        unipotent ((y.1 1 1 - 1) / y.1 1 0) := by
      apply sl2_ext <;> simp [mul_apply'] <;> field_simp <;>
        first | ring1 | linear_combination hdet | linear_combination -hdet
    rw [hy]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : x.1 1 0 = 0
  · have h00 : x.1 0 0 ≠ 0 := by
      intro h
      have := sl2_det x
      rw [h, hc] at this
      simp at this
    have hLA : (lMat 1 * x).1 1 0 ≠ 0 := by
      simp [mul_apply', hc, h00]
    have e : x = (lMat 1)⁻¹ * (lMat 1 * x) := by group
    rw [e]
    exact mul_mem (inv_mem (hL 1)) (key _ hLA)
  · exact key x hc

open Polynomial in
theorem exists_sq_add_sq [Finite F] (hodd : Odd (Nat.card F)) (x : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = x := by
  classical
  have := Fintype.ofFinite F
  have hodd' : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.1 hodd
  obtain ⟨a, b, hab⟩ : ∃ a b : F, (X ^ 2 : F[X]).eval a + (X ^ 2 - C x : F[X]).eval b = 0 :=
    FiniteField.exists_root_sum_quadratic (degree_X_pow 2)
      (degree_X_pow_sub_C (by decide) _) hodd'
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

theorem eq_bot_or_eq_upperSub [Finite F] (hodd : Odd (Nat.card F)) {Y : Subgroup (SL2m F)}
    (hY : Y ≤ upperSub F) (hn : ∀ d ∈ diagSub F, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = upperSub F := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have hyU : y ∈ upperSub F := hY hy
  have hys := eq_unipotent_of_mem_upperSub hyU
  set s := y.1 0 1 with hs
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 : y = 1 := by rw [hys, h0, unipotent_zero]
    exact hy1 (Subtype.ext h1)
  have hsq : ∀ a : F, unipotent (a ^ 2 * s) ∈ Y := by
    intro a
    by_cases ha : a = 0
    · rw [ha, zero_pow two_ne_zero, zero_mul, unipotent_zero]
      exact Y.one_mem
    · have hd : dg a a⁻¹ (mul_inv_cancel₀ ha) ∈ diagSub F := dg_mem_diagSub _ _ _
      have h1 := hn _ hd y hy
      have h2 := eq_unipotent_of_mem_upperSub (diag_conj_mem_upperSub hd hyU)
      rw [diag_conj_01 hd, dg_apply_00] at h2
      rw [h2, ← hs, ← pow_two] at h1
      exact h1
  have hall : ∀ r : F, unipotent r ∈ Y := by
    intro r
    obtain ⟨a, b, hab⟩ := exists_sq_add_sq hodd (r / s)
    have hr : r = a ^ 2 * s + b ^ 2 * s := by
      rw [← add_mul, hab, div_mul_cancel₀ _ hs0]
    rw [hr, unipotent_add]
    exact Y.mul_mem (hsq a) (hsq b)
  refine le_antisymm hY (fun x hx => ?_)
  rw [eq_unipotent_of_mem_upperSub hx]
  exact hall _

theorem eq_one_or_eq_w0_sq {g : SL2m F} (hg : g ∈ diagSub F)
    (hc : ∀ x ∈ upperSub F, g * x = x * g) : g = 1 ∨ g = w0 F ^ 2 := by
  obtain ⟨hg1, hg2⟩ := hg
  have hdet := sl2_det g
  rw [hg1, hg2] at hdet
  have h := congrArg (fun y : SL2m F => y.1 0 1) (hc (unipotent 1) (unipotent_mem_upperSub 1))
  simp [mul_apply', hg1] at h
  have hsq : (g.1 0 0 - 1) * (g.1 0 0 + 1) = 0 := by
    linear_combination hdet + g.1 0 0 * h
  rcases mul_eq_zero.1 hsq with h0 | h0
  · left
    have h00 : g.1 0 0 = 1 := sub_eq_zero.1 h0
    apply sl2_ext <;> simp [h00, hg1, hg2, ← h]
  · right
    have h00 : g.1 0 0 = -1 := eq_neg_of_add_eq_zero_left h0
    apply sl2_ext <;> simp [pow_two, mul_apply', w0, h00, hg1, hg2, ← h]

theorem conj_unipotent_00 (g : SL2m F) (s : F) :
    (g * unipotent s * g⁻¹).1 0 0 = 1 - g.1 0 0 * g.1 1 0 * s := by
  have hdet := sl2_det g
  simp only [mul_apply', inv_apply_00, inv_apply_10, unipotent_00, unipotent_01, unipotent_10,
    unipotent_11]
  linear_combination hdet

theorem conj_unipotent_01 (g : SL2m F) (s : F) :
    (g * unipotent s * g⁻¹).1 0 1 = g.1 0 0 * g.1 0 0 * s := by
  simp only [mul_apply', inv_apply_01, inv_apply_11, unipotent_00, unipotent_01, unipotent_10,
    unipotent_11]
  ring

theorem conj_unipotent_10 (g : SL2m F) (s : F) :
    (g * unipotent s * g⁻¹).1 1 0 = -(g.1 1 0 * g.1 1 0 * s) := by
  simp only [mul_apply', inv_apply_00, inv_apply_10, unipotent_00, unipotent_01, unipotent_10,
    unipotent_11]
  ring

theorem conj_unipotent_11 (g : SL2m F) (s : F) :
    (g * unipotent s * g⁻¹).1 1 1 = 1 + g.1 0 0 * g.1 1 0 * s := by
  have hdet := sl2_det g
  simp only [mul_apply', inv_apply_01, inv_apply_11, unipotent_00, unipotent_01, unipotent_10,
    unipotent_11]
  linear_combination hdet

theorem eq_upperSub_or_eq_lowerSub [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) {τ : SL2m F} (hτ : τ ∈ diagSub F)
    (hτ2 : τ.1 0 0 * τ.1 0 0 ≠ 1) {W : Subgroup (SL2m F)} (hW : Nat.card W = Nat.card F)
    (hn : ∀ x ∈ W, τ * x * τ⁻¹ ∈ W) : W = upperSub F ∨ W = lowerSub F := by
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hcard hW
  set V : Subgroup (SL2m F) := (upperSub F).map (MulAut.conj g).toMonoidHom with hV
  have hVmem : ∀ v ∈ V, ∃ r : F, v = g * unipotent r * g⁻¹ := by
    rintro v ⟨x, hx, rfl⟩
    exact ⟨x.1 0 1, by rw [← eq_unipotent_of_mem_upperSub hx]; simp⟩
  have hVW : V ≤ W := by
    intro v hv
    obtain ⟨r, rfl⟩ := hVmem v hv
    exact hg r
  have hVcard : Nat.card V = Nat.card F := by
    rw [hV, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_upperSub]
  have hVeq : V = W := Subgroup.eq_of_le_of_card_ge hVW (by rw [hVcard, hW])
  have hτM := hn _ (hg 1)
  rw [← hVeq] at hτM
  obtain ⟨r, hr⟩ := hVmem _ hτM
  have h00 : (τ * (g * unipotent 1 * g⁻¹) * τ⁻¹).1 0 0 = (g * unipotent r * g⁻¹).1 0 0 := by
    rw [hr]
  have h01 : (τ * (g * unipotent 1 * g⁻¹) * τ⁻¹).1 0 1 = (g * unipotent r * g⁻¹).1 0 1 := by
    rw [hr]
  rw [diag_conj_00 hτ, conj_unipotent_00, conj_unipotent_00] at h00
  rw [diag_conj_01 hτ, conj_unipotent_01, conj_unipotent_01] at h01
  by_cases hac : g.1 0 0 * g.1 1 0 = 0
  · rcases mul_eq_zero.1 hac with ha | hc
    · right
      have hle : V ≤ lowerSub F := by
        intro v hv
        obtain ⟨r', rfl⟩ := hVmem v hv
        refine ⟨?_, ?_, ?_⟩
        · rw [conj_unipotent_00, ha]; ring
        · rw [conj_unipotent_11, ha]; ring
        · rw [conj_unipotent_01, ha]; ring
      rw [← hVeq]
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hVcard, card_lowerSub])
    · left
      have hle : V ≤ upperSub F := by
        intro v hv
        obtain ⟨r', rfl⟩ := hVmem v hv
        refine ⟨?_, ?_, ?_⟩
        · rw [conj_unipotent_00, hc]; ring
        · rw [conj_unipotent_11, hc]; ring
        · rw [conj_unipotent_10, hc]; ring
      rw [← hVeq]
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hVcard, card_upperSub])
  · exfalso
    have ha : g.1 0 0 ≠ 0 := fun h => hac (by rw [h, zero_mul])
    have h1 : g.1 0 0 * g.1 1 0 * (r - 1) = 0 := by linear_combination h00
    have hr1 : r = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hac)
    rw [hr1] at h01
    apply hτ2
    have h2 : g.1 0 0 * g.1 0 0 * (τ.1 0 0 * τ.1 0 0 - 1) = 0 := by linear_combination h01
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (mul_ne_zero ha ha))

end CFSG.GH74.GLS.SP.Local.SL2Root
