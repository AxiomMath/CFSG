module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.Semidihedral.Local

open QuaternionGroup

section NormalForm

variable {H : Type*} [Group H] {m : ℕ} [NeZero m] {x y : H}

theorem pow_val_add_of_pow_eq_one (hx : x ^ (2 * m) = 1) (i j : ZMod (2 * m)) :
    x ^ (i + j).val = x ^ i.val * x ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem pow_val_neg_of_pow_eq_one (hx : x ^ (2 * m) = 1) (i : ZMod (2 * m)) :
    x ^ (-i).val = (x ^ i.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_val_add_of_pow_eq_one hx, neg_add_cancel, ZMod.val_zero,
    pow_zero]

theorem pow_val_sub_of_pow_eq_one (hx : x ^ (2 * m) = 1) (i j : ZMod (2 * m)) :
    x ^ (j - i).val = x ^ j.val * (x ^ i.val)⁻¹ := by
  rw [sub_eq_add_neg, pow_val_add_of_pow_eq_one hx, pow_val_neg_of_pow_eq_one hx]

omit [NeZero m] in
theorem pow_val_natCast_of_pow_eq_one (hx : x ^ (2 * m) = 1) (k : ℕ) :
    x ^ ((k : ZMod (2 * m))).val = x ^ k := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

theorem conj_pow_of_conj_eq_inv (hyx : y * x * y⁻¹ = x⁻¹) (k : ℕ) :
    y * x ^ k * y⁻¹ = (x ^ k)⁻¹ := by
  rw [← conj_pow, hyx, inv_pow]

@[expose] def normalFormFun (x y : H) : QuaternionGroup m → H
  | a i => x ^ i.val
  | xa i => y * x ^ i.val

theorem normalFormFun_mul (hx : x ^ (2 * m) = 1) (hy2 : y ^ 2 = x ^ m)
    (hyx : y * x * y⁻¹ = x⁻¹) (g h : QuaternionGroup m) :
    normalFormFun x y (g * h) = normalFormFun x y g * normalFormFun x y h := by
  have hyx' : y⁻¹ * x * y = x⁻¹ := by
    rw [← inv_inj, show (y⁻¹ * x * y)⁻¹ = y⁻¹ * x⁻¹ * y by group, inv_inv, ← hyx]
    group
  have hxy : ∀ k : ℕ, x ^ k * y = y * (x ^ k)⁻¹ := fun k => by
    have h : y⁻¹ * x ^ k * y = (x ^ k)⁻¹ := by
      have := conj_pow (a := y⁻¹) (b := x) (i := k)
      rw [inv_inv] at this
      rw [← this, hyx', inv_pow]
    calc x ^ k * y = y * (y⁻¹ * x ^ k * y) := by group
      _ = y * (x ^ k)⁻¹ := by rw [h]
  have hcomm : ∀ p q : ℕ, (x ^ p)⁻¹ * x ^ q = x ^ q * (x ^ p)⁻¹ := fun p q =>
    ((Commute.pow_pow_self x p q).inv_left).eq
  rcases g with i | i <;> rcases h with j | j
  · show x ^ (i + j).val = x ^ i.val * x ^ j.val
    exact pow_val_add_of_pow_eq_one hx i j
  · show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
    rw [pow_val_sub_of_pow_eq_one hx, ← mul_assoc (x ^ i.val), hxy, mul_assoc, hcomm]
  · show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
    rw [pow_val_add_of_pow_eq_one hx, mul_assoc]
  · show x ^ ((m : ZMod (2 * m)) + j - i).val = y * x ^ i.val * (y * x ^ j.val)
    rw [pow_val_sub_of_pow_eq_one hx, pow_val_add_of_pow_eq_one hx,
      pow_val_natCast_of_pow_eq_one hx]
    calc x ^ m * x ^ j.val * (x ^ i.val)⁻¹ = y ^ 2 * ((x ^ i.val)⁻¹ * x ^ j.val) := by
          rw [hy2, hcomm, mul_assoc]
      _ = y * (y * (x ^ i.val)⁻¹) * x ^ j.val := by rw [pow_two]; group
      _ = y * (x ^ i.val * y) * x ^ j.val := by rw [hxy]
      _ = y * x ^ i.val * (y * x ^ j.val) := by group

@[expose] noncomputable def normalFormHom (hx : x ^ (2 * m) = 1) (hy2 : y ^ 2 = x ^ m)
    (hyx : y * x * y⁻¹ = x⁻¹) : QuaternionGroup m →* H where
  toFun := normalFormFun x y
  map_one' := by
    show x ^ (0 : ZMod (2 * m)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := normalFormFun_mul hx hy2 hyx

end NormalForm

variable {H : Type*} [Group H] {m : ℕ}

theorem quaternion_eq_of_generators [NeZero m] {K : Type*} [Group K]
    {e₁ e₂ : QuaternionGroup m →* K} (h1 : e₁ (a 1) = e₂ (a 1)) (h2 : e₁ (xa 0) = e₂ (xa 0)) :
    e₁ = e₂ := by
  have ha : ∀ i : ZMod (2 * m), a i = (a 1 : QuaternionGroup m) ^ i.val := fun i => by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  have hxa : ∀ i : ZMod (2 * m), xa i = (xa 0 : QuaternionGroup m) * a i := fun i => by
    rw [xa_mul_a, zero_add]
  refine MonoidHom.ext fun g => ?_
  rcases g with i | i
  · rw [ha, map_pow, map_pow, h1]
  · rw [hxa, map_mul, map_mul, h2, ha, map_pow, map_pow, h1]

theorem quaternion_normal_form_isomorphism (hm : 1 ≤ m) {x y : H}
    (hgen : Subgroup.closure ({x, y} : Set H) = ⊤) (hx : orderOf x = 2 * m)
    (hy : y ∉ Subgroup.zpowers x) (hy2 : y ^ 2 = x ^ m) (hyx : y * x * y⁻¹ = x⁻¹) :
    (∃! e : QuaternionGroup m ≃* H, e (a 1) = x ∧ e (xa 0) = y) ∧
      ∀ e : QuaternionGroup m ≃* H, e (a 1) = x → e (xa 0) = y →
        ∀ i : ZMod (2 * m), e (a i) = x ^ i.val ∧ e (xa i) = y * x ^ i.val := by
  have : NeZero m := ⟨by omega⟩
  have hx2m : x ^ (2 * m) = 1 := by rw [← hx, pow_orderOf_eq_one]
  set φ := normalFormHom hx2m hy2 hyx with hφdef
  have hφa : ∀ i, φ (a i) = x ^ i.val := fun i => rfl
  have hφxa : ∀ i, φ (xa i) = y * x ^ i.val := fun i => rfl
  have hval1 : (1 : ZMod (2 * m)).val = 1 := ZMod.val_one'' (by omega)
  have hφ1 : φ (a 1) = x := by rw [hφa, hval1, pow_one]
  have hφ0 : φ (xa 0) = y := by rw [hφxa, ZMod.val_zero, pow_zero, mul_one]
  have hpowinj : ∀ i j : ZMod (2 * m), x ^ i.val = x ^ j.val → i = j := by
    intro i j hij
    rw [pow_inj_mod, hx, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)]
      at hij
    exact ZMod.val_injective _ hij
  have hinj : Function.Injective φ := by
    intro g h hgh
    rcases g with i | i <;> rcases h with j | j
    · rw [hφa, hφa] at hgh
      rw [hpowinj i j hgh]
    · rw [hφa, hφxa] at hgh
      exfalso
      apply hy
      have : y = x ^ i.val * (x ^ j.val)⁻¹ := by rw [hgh]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
    · rw [hφxa, hφa] at hgh
      exfalso
      apply hy
      have : y = x ^ j.val * (x ^ i.val)⁻¹ := by rw [← hgh]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
    · rw [hφxa, hφxa, mul_right_inj] at hgh
      rw [hpowinj i j hgh]
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨a 1, hφ1⟩
    · exact ⟨xa 0, hφ0⟩
  let e : QuaternionGroup m ≃* H := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ g, e g = φ g := fun g => rfl
  have huniq : ∀ e' : QuaternionGroup m ≃* H, e' (a 1) = x → e' (xa 0) = y → e' = e := by
    intro e' h1 h2
    have hhom : e'.toMonoidHom = e.toMonoidHom :=
      quaternion_eq_of_generators (by simp [h1, he, hφ1]) (by simp [h2, he, hφ0])
    exact MulEquiv.ext fun g => DFunLike.congr_fun hhom g
  refine ⟨⟨e, ⟨by rw [he, hφ1], by rw [he, hφ0]⟩, fun e' ⟨h1, h2⟩ => huniq e' h1 h2⟩,
    fun e' h1 h2 i => ?_⟩
  rw [huniq e' h1 h2, he, he, hφa, hφxa]
  exact ⟨rfl, rfl⟩

end CFSG.Semidihedral.Local
