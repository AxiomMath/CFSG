module

public import CFSG.ClassicalGroups.SpecialLinear.TvModGroup

public section

namespace CFSG.ClassicalGroups.SpecialLinear.TvMod

open Matrix CFSG.LargeExtraspecial.A2Mod
open scoped commutatorElement

variable {n : ℕ}

@[expose] def tvCoreGen (v₀ φ₀ : Fin n → ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  {g | ∃ u ψ : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 ∧ ψ ⬝ᵥ v₀ = 0 ∧ ψ ⬝ᵥ u = 0 ∧ tv u ψ = g}

theorem mem_tvCoreGen {v₀ φ₀ : Fin n → ZMod 2} {g : SpecialLinearGroup (Fin n) (ZMod 2)} :
    g ∈ tvCoreGen v₀ φ₀ ↔
      ∃ u ψ : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 ∧ ψ ⬝ᵥ v₀ = 0 ∧ ψ ⬝ᵥ u = 0 ∧ tv u ψ = g :=
  Iff.rfl

@[expose] def tvCore (v₀ φ₀ : Fin n → ZMod 2) : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  Subgroup.closure (tvCoreGen v₀ φ₀)

theorem tvCore_eq_closure (v₀ φ₀ : Fin n → ZMod 2) :
    tvCore v₀ φ₀ = Subgroup.closure (tvCoreGen v₀ φ₀) :=
  rfl

theorem subset_tvCore (v₀ φ₀ : Fin n → ZMod 2) : tvCoreGen v₀ φ₀ ⊆ tvCore v₀ φ₀ :=
  Subgroup.subset_closure

theorem mulVec_eq_of_mem_tvCore {v₀ φ₀ : Fin n → ZMod 2}
    {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ tvCore v₀ φ₀) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀ = v₀ := by
  rw [tvCore_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, ψ, -, hψv, -, rfl⟩ := mem_tvCoreGen.mp hx
    exact tv_mulVec_of_dotProduct_eq_zero hψv
  | one => rw [SpecialLinearGroup.coe_one, one_mulVec]
  | mul x y _ _ hx hy => rw [sl_mulVec_mul, hy, hx]
  | inv x _ hx =>
    calc ((x⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀
        = ((x⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀) := by rw [hx]
      _ = v₀ := sl_inv_mulVec_mulVec x v₀

theorem contra_eq_of_mem_tvCore {v₀ φ₀ : Fin n → ZMod 2}
    {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ tvCore v₀ φ₀) : contra g φ₀ = φ₀ := by
  rw [tvCore_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, ψ, hφu, -, -, rfl⟩ := mem_tvCoreGen.mp hx
    exact contra_tv_of_dotProduct_eq_zero hφu
  | one => exact contra_one φ₀
  | mul x y _ _ hx hy => rw [contra_mul, hy, hx]
  | inv x _ hx =>
    calc contra x⁻¹ φ₀ = contra x⁻¹ (contra x φ₀) := by rw [hx]
      _ = φ₀ := contra_inv_contra x φ₀

theorem commute_tv_of_mem_tvCore {v₀ φ₀ : Fin n → ZMod 2}
    {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ tvCore v₀ φ₀) : Commute g (tv v₀ φ₀) := by
  have h := conj_tv g v₀ φ₀
  rw [mulVec_eq_of_mem_tvCore hg, contra_eq_of_mem_tvCore hg] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem exists_tv_eq_commutatorElement (hn : 5 ≤ n) {v φ w ψ : Fin n → ZMod 2}
    (hψw : ψ ⬝ᵥ w = 0) :
    ∃ u χ : Fin n → ZMod 2, φ ⬝ᵥ u = 0 ∧ ψ ⬝ᵥ u = 0 ∧ χ ⬝ᵥ v = 0 ∧ χ ⬝ᵥ w = 0 ∧
      tv w ψ = ⁅tv w χ, tv u ψ⁆ := by
  classical
  obtain ⟨u, hφu, hψu, hu⟩ : ∃ u : Fin n → ZMod 2, φ ⬝ᵥ u = 0 ∧ ψ ⬝ᵥ u = 0 ∧
      u ∉ Submodule.span (ZMod 2) {v, w} := by
    by_contra hcon'
    have hcon : ∀ x : Fin n → ZMod 2, φ ⬝ᵥ x = 0 → ψ ⬝ᵥ x = 0 →
        x ∈ Submodule.span (ZMod 2) {v, w} :=
      fun x h1 h2 => by_contra fun h3 => hcon' ⟨x, h1, h2, h3⟩
    set s := Finset.univ.filter fun x : Fin n → ZMod 2 => ∀ i, x ⬝ᵥ ![φ, ψ] i = 0 with hs
    have hcard : 8 ≤ s.card := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      have h3 : 2 ^ 3 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans h3 (card_annihilator_ge ![φ, ψ])
    have hsub : s ⊆ ({0, v, w, v + w} : Finset (Fin n → ZMod 2)) := by
      intro x hx
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hφx : φ ⬝ᵥ x = 0 := by rw [dotProduct_comm]; simpa using hx 0
      have hψx : ψ ⬝ᵥ x = 0 := by rw [dotProduct_comm]; simpa using hx 1
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (hcon x hφx hψx)
      rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
        rcases zmodTwo_eq_zero_or_one b with rfl | rfl <;> simp
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_four (a := (0 : Fin n → ZMod 2)) (b := v) (c := w) (d := v + w)
    omega
  obtain ⟨f, hfu, hfle⟩ := Submodule.exists_le_ker_of_notMem hu
  set χ : Fin n → ZMod 2 := (dotProductEquiv (ZMod 2) (Fin n)).symm f with hχ
  have hχdot : ∀ x, χ ⬝ᵥ x = f x := fun x => by
    rw [← dotProductEquiv_apply_apply, hχ, LinearEquiv.apply_symm_apply]
  have hχv : χ ⬝ᵥ v = 0 := by
    rw [hχdot]
    exact LinearMap.mem_ker.mp (hfle (Submodule.subset_span (by simp)))
  have hχw : χ ⬝ᵥ w = 0 := by
    rw [hχdot]
    exact LinearMap.mem_ker.mp (hfle (Submodule.subset_span (by simp)))
  have hχu : χ ⬝ᵥ u = 1 := by
    rw [hχdot]
    exact zmodTwo_eq_one_of_ne_zero hfu
  have hy : tv w χ * tv u ψ * tv w χ = tv (u + w) ψ := by
    have := conj_tv (tv w χ) u ψ
    rw [tv_inv_eq_self, tv_mulVec hχw, contra_tv_of_dotProduct_eq_zero hψw, hχu, one_smul] at this
    exact this
  refine ⟨u, χ, hφu, hψu, hχv, hχw, ?_⟩
  have hψuw : ψ ⬝ᵥ (u + w) = 0 := by rw [dotProduct_add, hψu, hψw, add_zero]
  have e : u + w + u = w := by rw [add_comm u w, add_assoc, ZModModule.add_self, add_zero]
  rw [commutatorElement_def, tv_inv_eq_self, tv_inv_eq_self, hy, tv_mul_tv_right hψuw hψu, e]

theorem commutator_tvCore (hn : 5 ≤ n) (v₀ φ₀ : Fin n → ZMod 2) :
    ⁅tvCore v₀ φ₀, tvCore v₀ φ₀⁆ = tvCore v₀ φ₀ := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  · rw [tvCore_eq_closure, Subgroup.closure_le]
    rintro _ ⟨u, ψ, hφu, hψv, hψu, rfl⟩
    obtain ⟨u', χ, hφu', hψu', hχv, hχu, h⟩ :=
      exists_tv_eq_commutatorElement hn (v := v₀) (φ := φ₀) (w := u) (ψ := ψ) hψu
    rw [h]
    exact Subgroup.commutator_mem_commutator (subset_tvCore v₀ φ₀ ⟨u, χ, hφu, hχv, hχu, rfl⟩)
      (subset_tvCore v₀ φ₀ ⟨u', ψ, hφu', hψv, hψu', rfl⟩)

private theorem eq_of_add_eq_zero' {x y : Fin n → ZMod 2} (h : x + y = 0) : x = y := by
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
  exact h

private theorem eq_add_of_add_eq {x y z : Fin n → ZMod 2} (h : x + y = z) : x = y + z := by
  rw [← h, add_left_comm, ZModModule.add_self, add_zero]

private theorem comm_of_sq_eq_one {G : Type*} [Group G] {A : Subgroup G}
    (hA : ∀ a ∈ A, a * a = 1) {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hA _ (A.mul_mem ha hb))
  rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hA a ha),
    inv_eq_of_mul_eq_one_right (hA b hb)] at h1
  exact h1.symm

private theorem eq_of_forall_dotProduct_eq_zero {v w y : Fin n → ZMod 2}
    (h : ∀ χ : Fin n → ZMod 2, χ ⬝ᵥ v = 0 → χ ⬝ᵥ w = 0 → χ ⬝ᵥ y = 0) :
    y = 0 ∨ y = v ∨ y = w ∨ y = v + w := by
  by_cases hy : y ∈ Submodule.span (ZMod 2) {v, w}
  · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
      rcases zmodTwo_eq_zero_or_one b with rfl | rfl <;> simp
  · obtain ⟨f, hfy, hfle⟩ := Submodule.exists_le_ker_of_notMem hy
    set χ : Fin n → ZMod 2 := (dotProductEquiv (ZMod 2) (Fin n)).symm f with hχ
    have hχdot : ∀ x, χ ⬝ᵥ x = f x := fun x => by
      rw [← dotProductEquiv_apply_apply, hχ, LinearEquiv.apply_symm_apply]
    have hχv : χ ⬝ᵥ v = 0 := by
      rw [hχdot]
      exact LinearMap.mem_ker.mp (hfle (Submodule.subset_span (by simp)))
    have hχw : χ ⬝ᵥ w = 0 := by
      rw [hχdot]
      exact LinearMap.mem_ker.mp (hfle (Submodule.subset_span (by simp)))
    exact absurd (by rw [← hχdot]; exact h χ hχv hχw) hfy

private theorem eq_of_forall_dotProduct_eq_zero' {φ ψ χ : Fin n → ZMod 2}
    (h : ∀ x : Fin n → ZMod 2, φ ⬝ᵥ x = 0 → ψ ⬝ᵥ x = 0 → χ ⬝ᵥ x = 0) :
    χ = 0 ∨ χ = φ ∨ χ = ψ ∨ χ = φ + ψ :=
  eq_of_forall_dotProduct_eq_zero fun x h1 h2 => by
    rw [dotProduct_comm] at h1 h2 ⊢
    exact h x h1 h2

private theorem eq_of_forall_dotProduct_eq_zero_single {v y : Fin n → ZMod 2}
    (h : ∀ χ : Fin n → ZMod 2, χ ⬝ᵥ v = 0 → χ ⬝ᵥ y = 0) : y = 0 ∨ y = v := by
  rcases eq_of_forall_dotProduct_eq_zero (v := v) (w := v) (y := y)
    (fun χ h1 _ => h χ h1) with h | h | h | h
  · exact .inl h
  · exact .inr h
  · exact .inr h
  · exact .inl (by rw [h, ZModModule.add_self])

private theorem fix_of_commute {v₀ φ₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0)
    (h₀ : φ₀ ⬝ᵥ v₀ = 0) {a : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hc : a * tv v₀ φ₀ = tv v₀ φ₀ * a) :
    (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀ = v₀ ∧ contra a φ₀ = φ₀ := by
  have h1 : tv ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀) (contra a φ₀) = tv v₀ φ₀ := by
    rw [← conj_tv, hc, mul_inv_cancel_right]
  have h2 : contra a φ₀ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀) = 0 := by
    rw [contra_dotProduct_mulVec, h₀]
  obtain ⟨e1, e2⟩ := (tv_eq_tv_iff hv₀ hφ₀ h₀ h2).mp h1.symm
  exact ⟨e1.symm, e2.symm⟩

private theorem dotProduct_mulVec_eq_zero {v₀ φ₀ : Fin n → ZMod 2}
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hA : ∀ a ∈ A, a * a = 1)
    (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    {a : SpecialLinearGroup (Fin n) (ZMod 2)} (ha : a ∈ A) {u ψ : Fin n → ZMod 2}
    (hφu : φ₀ ⬝ᵥ u = 0) (hψv : ψ ⬝ᵥ v₀ = 0) (hψu : ψ ⬝ᵥ u = 0) :
    ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = 0 := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA a ha)
  have h1 : tv u ψ * a * (tv u ψ)⁻¹ ∈ A := hY _ ⟨u, ψ, hφu, hψv, hψu, rfl⟩ a ha
  have h2 : a * (tv u ψ * a * (tv u ψ)⁻¹) ∈ A := A.mul_mem ha h1
  have h3 : a * (tv u ψ * a * (tv u ψ)⁻¹) =
      tv ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) (contra a ψ) * tv u ψ := by
    rw [tv_inv_eq_self, ← conj_tv, hinv]
    simp only [mul_assoc]
  have hsq := hA _ h2
  rw [h3] at hsq
  rcases zmodTwo_eq_zero_or_one (ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u)) with h | h
  · exact h
  exfalso
  have hc1 : contra a ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = 0 := by
    rw [contra_dotProduct_mulVec, hψu]
  have hc2 : contra a ψ ⬝ᵥ u = 1 := by
    have := contra_dotProduct_mulVec a ψ
      (((a⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u)
    rw [sl_mulVec_inv_mulVec, hinv] at this
    rw [this, h]
  have hdvd : 3 ∣ 2 := by
    rw [← orderOf_tv_mul_tv hc1 hψu hc2 h]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  omega

private theorem mulVec_add_cases {v₀ φ₀ : Fin n → ZMod 2} {a : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hav : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀ = v₀)
    (h2 : ∀ u ψ : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 → ψ ⬝ᵥ v₀ = 0 → ψ ⬝ᵥ u = 0 →
      ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = 0)
    {x : Fin n → ZMod 2} (hx : φ₀ ⬝ᵥ x = 0) :
    (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x = 0 ∨
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x = v₀ := by
  have key : ∀ χ : Fin n → ZMod 2, χ ⬝ᵥ v₀ = 0 → χ ⬝ᵥ x = 0 →
      χ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x) = 0 := fun χ h1 h3 => by
    rw [dotProduct_add, h2 x χ hx h1 h3, h3, add_zero]
  rcases eq_of_forall_dotProduct_eq_zero key with h | h | h | h
  · exact .inl h
  · exact .inr h
  · refine .inl ?_
    have hx0 : x = 0 := (sl_mulVec_eq_zero_iff a).mp (add_eq_right.mp h)
    rw [hx0, mulVec_zero, add_zero]
  · refine .inl ?_
    have h' : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = v₀ := add_right_cancel h
    have hxv : x = v₀ := sl_mulVec_injective a (h'.trans hav.symm)
    rw [h', hxv, ZModModule.add_self]

private theorem contra_add_cases {v₀ φ₀ : Fin n → ZMod 2} {a : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hsq : a * a = 1) (hcφ : contra a φ₀ = φ₀)
    (h2 : ∀ u ψ : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 → ψ ⬝ᵥ v₀ = 0 → ψ ⬝ᵥ u = 0 →
      ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = 0)
    {ψ : Fin n → ZMod 2} (hψ : ψ ⬝ᵥ v₀ = 0) :
    contra a ψ + ψ = 0 ∨ contra a ψ + ψ = φ₀ := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
  have key : ∀ u : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 → ψ ⬝ᵥ u = 0 → (contra a ψ + ψ) ⬝ᵥ u = 0 :=
    fun u h1 h3 => by
      have e : contra a ψ ⬝ᵥ u = ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) := by
        have := contra_dotProduct_mulVec a ψ
          (((a⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u)
        rw [sl_mulVec_inv_mulVec, hinv] at this
        exact this
      rw [add_dotProduct, e, h2 u ψ h1 hψ h3, h3, add_zero]
  rcases eq_of_forall_dotProduct_eq_zero' key with h | h | h | h
  · exact .inl h
  · exact .inr h
  · refine .inl ?_
    have hψ0 : ψ = 0 := (contra_eq_zero_iff a).mp (add_eq_right.mp h)
    rw [hψ0, contra_zero, add_zero]
  · refine .inl ?_
    have h' : contra a ψ = φ₀ := add_right_cancel h
    have hψφ : ψ = φ₀ := contra_injective a (h'.trans hcφ.symm)
    rw [h', hψφ, ZModModule.add_self]

private theorem exists_form_apply (a : SpecialLinearGroup (Fin n) (ZMod 2)) (i : Fin n) :
    ∃ μ : Fin n → ZMod 2, ∀ x : Fin n → ZMod 2,
      μ ⬝ᵥ x = ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x) i := by
  refine ⟨((a : Matrix (Fin n) (Fin n) (ZMod 2)) + 1).row i, fun x => ?_⟩
  rw [← Matrix.mulVec_apply, add_mulVec, one_mulVec]

private theorem mem_pointGroup_of_contra_eq {v₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    {a : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hav : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀ = v₀)
    (hfix : ∀ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v₀ = 0 → contra a ψ = ψ) : a ∈ pointGroup v₀ := by
  obtain ⟨i, hi⟩ := exists_apply_eq_one_of_ne_zero hv₀
  obtain ⟨φ, hφ⟩ := exists_form_apply a i
  have hx : ∀ x : Fin n → ZMod 2, (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x = 0 ∨
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x = v₀ := fun x =>
    eq_of_forall_dotProduct_eq_zero_single fun ψ hψ => by
      rw [dotProduct_add, ← contra_dotProduct_mulVec a ψ x, hfix ψ hψ, ZModModule.add_self]
  have hφv : φ ⬝ᵥ v₀ = 0 := by rw [hφ, hav, ZModModule.add_self]; rfl
  have hd : ∀ x : Fin n → ZMod 2,
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x + x = (φ ⬝ᵥ x) • v₀ := fun x => by
    rcases hx x with h | h
    · rw [hφ x, h]
      simp
    · rw [hφ x, h, hi, one_smul]
  refine mem_pointGroup.mpr ⟨φ, hφv, Subtype.ext (Matrix.ext_iff_mulVec.mpr fun x => ?_)⟩
  rw [tv_mulVec hφv, ← hd x, add_comm ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) x,
    ← add_assoc, ZModModule.add_self, zero_add]

private theorem exists_ne_zero_ne_dotProduct_eq_zero (hn : 5 ≤ n) (e y₁ y₂ y₃ : Fin n → ZMod 2) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧ x ≠ e ∧ x ⬝ᵥ y₁ = 0 ∧ x ⬝ᵥ y₂ = 0 ∧ x ⬝ᵥ y₃ = 0 := by
  obtain ⟨x, x', hx, hx', hne, h, h'⟩ :=
    exists_two_ne_zero_annihilator (k := 3) (by omega) ![y₁, y₂, y₃]
  by_cases hxe : x = e
  · exact ⟨x', hx', fun h'' => hne (hxe.trans h''.symm), by simpa using h' 0, by simpa using h' 1,
      by simpa using h' 2⟩
  · exact ⟨x, hx, hxe, by simpa using h 0, by simpa using h 1, by simpa using h 2⟩

private theorem exists_tv_mem_of_not_mem_pointGroup (hn : 5 ≤ n) {v₀ φ₀ : Fin n → ZMod 2}
    (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0) (h₀ : φ₀ ⬝ᵥ v₀ = 0)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hA : ∀ a ∈ A, a * a = 1)
    (hτ : tv v₀ φ₀ ∈ A) (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    {a : SpecialLinearGroup (Fin n) (ZMod 2)} (ha : a ∈ A) (hna : a ∉ pointGroup v₀) :
    ∃ u : Fin n → ZMod 2, u ≠ 0 ∧ u ≠ v₀ ∧ φ₀ ⬝ᵥ u = 0 ∧ tv u φ₀ ∈ A := by
  have hsq := hA a ha
  obtain ⟨hav, hcφ⟩ := fix_of_commute hv₀ hφ₀ h₀ (comm_of_sq_eq_one hA ha hτ)
  have h2 : ∀ u ψ : Fin n → ZMod 2, φ₀ ⬝ᵥ u = 0 → ψ ⬝ᵥ v₀ = 0 → ψ ⬝ᵥ u = 0 →
      ψ ⬝ᵥ ((a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = 0 :=
    fun u ψ h1 h2 h3 => dotProduct_mulVec_eq_zero hA hY ha h1 h2 h3
  obtain ⟨ψ, hψv, hψa⟩ : ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v₀ = 0 ∧ contra a ψ + ψ = φ₀ := by
    by_contra hcon
    refine hna (mem_pointGroup_of_contra_eq hv₀ hav fun ψ hψ => ?_)
    rcases contra_add_cases hsq hcφ h2 hψ with h | h
    · exact eq_of_add_eq_zero' h
    · exact absurd ⟨ψ, hψ, h⟩ hcon
  obtain ⟨i, hi⟩ := exists_apply_eq_one_of_ne_zero hv₀
  obtain ⟨μ, hμ⟩ := exists_form_apply a i
  obtain ⟨u, hu0, huv, hu1, hu2, hu3⟩ := exists_ne_zero_ne_dotProduct_eq_zero hn v₀ φ₀ ψ μ
  have hφu : φ₀ ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact hu1
  have hψu : ψ ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact hu2
  have hau : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u := by
    rcases mulVec_add_cases hav h2 hφu with h | h
    · exact eq_of_add_eq_zero' h
    · have h4 := hμ u
      rw [h, hi, dotProduct_comm, hu3] at h4
      exact absurd h4 zero_ne_one
  have hy : tv u ψ ∈ tvCoreGen v₀ φ₀ := ⟨u, ψ, hφu, hψv, hψu, rfl⟩
  have h3 : a * tv u ψ * a⁻¹ = tv u (ψ + φ₀) := by
    rw [conj_tv, hau, eq_add_of_add_eq hψa]
  have h4 : tv u ψ * a * (tv u ψ)⁻¹ * a⁻¹ ∈ A := A.mul_mem (hY _ hy a ha) (A.inv_mem ha)
  have h5 : tv u ψ * a * (tv u ψ)⁻¹ * a⁻¹ = tv u φ₀ := by
    have e : tv u ψ * a * (tv u ψ)⁻¹ * a⁻¹ = tv u ψ * (a * tv u ψ * a⁻¹) := by
      rw [tv_inv_eq_self]
      simp only [mul_assoc]
    rw [e, h3, tv_mul_tv_left hψu (by rw [add_dotProduct, hψu, hφu, add_zero]), ← add_assoc,
      ZModModule.add_self, zero_add]
  exact ⟨u, hu0, huv, hφu, h5 ▸ h4⟩

private theorem exists_tv_mem_of_not_mem_hyperplaneGroup (hn : 5 ≤ n) {v₀ φ₀ : Fin n → ZMod 2}
    (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0) (h₀ : φ₀ ⬝ᵥ v₀ = 0)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hA : ∀ a ∈ A, a * a = 1)
    (hτ : tv v₀ φ₀ ∈ A) (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    {b : SpecialLinearGroup (Fin n) (ZMod 2)} (hb : b ∈ A) (hnb : b ∉ hyperplaneGroup φ₀) :
    ∃ χ : Fin n → ZMod 2, χ ≠ 0 ∧ χ ≠ φ₀ ∧ χ ⬝ᵥ v₀ = 0 ∧ tv v₀ χ ∈ A := by
  obtain ⟨A', hmem⟩ : ∃ A' : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)),
      ∀ g, g ∈ A' ↔ invTranspose g ∈ A :=
    ⟨A.comap invTranspose.toMonoidHom, fun g => Iff.rfl⟩
  have hA' : ∀ a ∈ A', a * a = 1 := by
    intro a ha
    have h := hA _ ((hmem a).mp ha)
    rw [← map_mul invTranspose] at h
    exact invTranspose.injective (h.trans (map_one invTranspose).symm)
  have hτ' : tv φ₀ v₀ ∈ A' := (hmem _).mpr (by rw [invTranspose_tv]; exact hτ)
  have hY' : ∀ y ∈ tvCoreGen φ₀ v₀, ∀ a ∈ A', y * a * y⁻¹ ∈ A' := by
    intro y hy a ha
    obtain ⟨u, ψ, h1, h2, h3, rfl⟩ := mem_tvCoreGen.mp hy
    refine (hmem _).mpr ?_
    rw [map_mul, map_mul, map_inv, invTranspose_tv]
    exact hY _ (mem_tvCoreGen.mpr ⟨ψ, u, by rwa [dotProduct_comm] at h2,
      by rwa [dotProduct_comm] at h1, by rwa [dotProduct_comm] at h3, rfl⟩) _ ((hmem a).mp ha)
  have hna' : invTranspose b ∉ pointGroup φ₀ := by
    intro hb'
    obtain ⟨ψ, hψ, he⟩ := mem_pointGroup.mp hb'
    refine hnb (mem_hyperplaneGroup.mpr ⟨ψ, by rwa [dotProduct_comm] at hψ, ?_⟩)
    rw [← invTranspose_tv, he, invTranspose_invTranspose]
  obtain ⟨χ, hχ0, hχφ, hχv, hτχ⟩ := exists_tv_mem_of_not_mem_pointGroup hn hφ₀ hv₀
    (by rwa [dotProduct_comm] at h₀) hA' hτ' hY'
    ((hmem _).mpr (by rw [invTranspose_invTranspose]; exact hb)) hna'
  refine ⟨χ, hχ0, hχφ, by rwa [dotProduct_comm] at hχv, ?_⟩
  have h := (hmem _).mp hτχ
  rwa [invTranspose_tv] at h

private theorem dotProduct_eq_zero_of_commute {v₀ φ₀ χ w : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    (hφ₀ : φ₀ ≠ 0) (h₀ : φ₀ ⬝ᵥ v₀ = 0) (hχv : χ ⬝ᵥ v₀ = 0) (hw : φ₀ ⬝ᵥ w = 0)
    (hc : tv w φ₀ * tv v₀ χ = tv v₀ χ * tv w φ₀) : χ ⬝ᵥ w = 0 := by
  have h1 : tv v₀ (χ - (χ ⬝ᵥ w) • φ₀) = tv v₀ χ := by
    have h := conj_tv (tv w φ₀) v₀ χ
    rw [hc, mul_inv_cancel_right, tv_mulVec_of_dotProduct_eq_zero h₀, contra_tv hw] at h
    exact h.symm
  have h2 : (χ - (χ ⬝ᵥ w) • φ₀) ⬝ᵥ v₀ = 0 := by
    rw [sub_dotProduct, smul_dotProduct, hχv, h₀, smul_zero, sub_zero]
  exact (smul_eq_zero.mp (sub_eq_self.mp (tv_right_injective hv₀ h2 hχv h1))).resolve_right hφ₀

private theorem false_of_mem_of_mem {v₀ φ₀ u χ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0)
    (h₀ : φ₀ ⬝ᵥ v₀ = 0) {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ a ∈ A, a * a = 1) (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hu0 : u ≠ 0) (huv : u ≠ v₀) (hφu : φ₀ ⬝ᵥ u = 0) (hτu : tv u φ₀ ∈ A)
    (hχ0 : χ ≠ 0) (hχφ : χ ≠ φ₀) (hχv : χ ⬝ᵥ v₀ = 0) (hτχ : tv v₀ χ ∈ A) : False := by
  have hχu : χ ⬝ᵥ u = 0 :=
    dotProduct_eq_zero_of_commute hv₀ hφ₀ h₀ hχv hφu (comm_of_sq_eq_one hA hτu hτχ)
  obtain ⟨ψ, hψv, hψu⟩ := exists_dotProduct_eq_zero_eq_one hu0 huv
  obtain ⟨x, hφx, hψx, hχx⟩ : ∃ x : Fin n → ZMod 2, φ₀ ⬝ᵥ x = 0 ∧ ψ ⬝ᵥ x = 0 ∧ χ ⬝ᵥ x ≠ 0 := by
    by_contra hcon'
    have hcon : ∀ x : Fin n → ZMod 2, φ₀ ⬝ᵥ x = 0 → ψ ⬝ᵥ x = 0 → χ ⬝ᵥ x = 0 :=
      fun x h1 h2 => by_contra fun h3 => hcon' ⟨x, h1, h2, h3⟩
    rcases eq_of_forall_dotProduct_eq_zero' hcon with h | h | h | h
    · exact hχ0 h
    · exact hχφ h
    · rw [h, hψu] at hχu
      exact one_ne_zero hχu
    · rw [h, add_dotProduct, hφu, hψu, zero_add] at hχu
      exact one_ne_zero hχu
  have h1 := hY _ (mem_tvCoreGen.mpr ⟨x, ψ, hφx, hψv, hψx, rfl⟩) _ hτu
  rw [conj_tv, tv_mulVec hψx, contra_tv_of_dotProduct_eq_zero hφx, hψu, one_smul] at h1
  have h2 : χ ⬝ᵥ (u + x) = 0 := dotProduct_eq_zero_of_commute hv₀ hφ₀ h₀ hχv
    (by rw [dotProduct_add, hφu, hφx, add_zero]) (comm_of_sq_eq_one hA h1 hτχ)
  rw [dotProduct_add, hχu, zero_add] at h2
  exact hχx h2

theorem le_pointGroup_or_le_hyperplaneGroup (hn : 5 ≤ n) {v₀ φ₀ : Fin n → ZMod 2}
    (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0) (h₀ : φ₀ ⬝ᵥ v₀ = 0)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ a ∈ A, a * a = 1) (hτ : tv v₀ φ₀ ∈ A)
    (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    A ≤ pointGroup v₀ ∨ A ≤ hyperplaneGroup φ₀ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hna, hnb⟩ := hcon
  obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.mp hna
  obtain ⟨b, hb, hb'⟩ := SetLike.not_le_iff_exists.mp hnb
  obtain ⟨u, hu0, huv, hφu, hτu⟩ :=
    exists_tv_mem_of_not_mem_pointGroup hn hv₀ hφ₀ h₀ hA hτ hY ha ha'
  obtain ⟨χ, hχ0, hχφ, hχv, hτχ⟩ :=
    exists_tv_mem_of_not_mem_hyperplaneGroup hn hv₀ hφ₀ h₀ hA hτ hY hb hb'
  exact false_of_mem_of_mem hv₀ hφ₀ h₀ hA hY hu0 huv hφu hτu hχ0 hχφ hχv hτχ

end CFSG.ClassicalGroups.SpecialLinear.TvMod
