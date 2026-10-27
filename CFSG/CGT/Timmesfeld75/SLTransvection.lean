module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.CGT.Timmesfeld75

open Module LinearMap
open scoped MatrixGroups Matrix

section Abstract

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_equiv_apply_eq_of_ne_zero {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {p q : W} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ σ : W ≃ₗ[F] W, σ p = q := by
  let e : (F ∙ p) ≃ₗ[F] (F ∙ q) :=
    (LinearEquiv.toSpanNonzeroSingleton F W p hp).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton F W q hq)
  obtain ⟨σ, hσ⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨σ, ?_⟩
  have h := hσ ⟨p, Submodule.mem_span_singleton_self p⟩
  have h1 : (LinearEquiv.toSpanNonzeroSingleton F W p hp).symm
      ⟨p, Submodule.mem_span_singleton_self p⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have h2 : e ⟨p, Submodule.mem_span_singleton_self p⟩ =
      ⟨q, Submodule.mem_span_singleton_self q⟩ := by
    simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_one]
  rw [← h, h2]

theorem exists_apply_eq_one_of_ne_zero {f : Dual F V} (hf : f ≠ 0) : ∃ e : V, f e = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  exact ⟨(f w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩

theorem exists_equiv_flag [FiniteDimensional F V] {f₁ f₂ : Dual F V} {v₁ v₂ : V}
    (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (h₁ : f₁ v₁ = 0)
    (h₂ : f₂ v₂ = 0) :
    ∃ (g : V ≃ₗ[F] V) (c : F), c ≠ 0 ∧ g v₁ = v₂ ∧ ∀ x, f₂ (g x) = c * f₁ x := by
  have hr₁ := Module.Dual.finrank_ker_add_one_of_ne_zero hf₁
  have hr₂ := Module.Dual.finrank_ker_add_one_of_ne_zero hf₂
  let ι : (ker f₁) ≃ₗ[F] (ker f₂) := LinearEquiv.ofFinrankEq _ _ (by omega)
  let a₁ : ker f₁ := ⟨v₁, LinearMap.mem_ker.2 h₁⟩
  let b₂ : ker f₂ := ⟨v₂, LinearMap.mem_ker.2 h₂⟩
  have ha₁ : a₁ ≠ 0 := fun h => hv₁ (congrArg Subtype.val h)
  have hb₂ : b₂ ≠ 0 := fun h => hv₂ (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := exists_equiv_apply_eq_of_ne_zero (F := F) (W := ker f₂)
    (p := ι a₁) (q := b₂) (fun h => ha₁ (ι.map_eq_zero_iff.1 h)) hb₂
  let k : (ker f₁) ≃ₗ[F] (ker f₂) := ι.trans σ
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq k
  obtain ⟨e₁, he₁⟩ := exists_apply_eq_one_of_ne_zero hf₁
  have hgv : g v₁ = v₂ := by
    have := hg a₁
    have hk : k a₁ = b₂ := hσ
    rw [hk] at this
    exact this.symm
  have hker : ∀ x, f₁ x = 0 → f₂ (g x) = 0 := by
    intro x hx
    have := hg ⟨x, LinearMap.mem_ker.2 hx⟩
    simp [← this]
  have hfun : ∀ x, f₂ (g x) = f₂ (g e₁) * f₁ x := by
    intro x
    have h0 : f₁ (x - f₁ x • e₁) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, he₁, mul_one, sub_self]
    have h3 := hker _ h0
    rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul] at h3
    rw [mul_comm]
    linear_combination h3
  refine ⟨g, f₂ (g e₁), ?_, hgv, hfun⟩
  intro hc
  obtain ⟨w, hw⟩ : ∃ w, f₂ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf₂ (LinearMap.ext h)
  apply hw
  have := hfun (g.symm w)
  rw [LinearEquiv.apply_symm_apply, hc, zero_mul] at this
  exact this

theorem exists_scale_equiv [FiniteDimensional F V] {f : Dual F V} {v : V} (hf : f ≠ 0) (hv : v ≠ 0)
    (hfv : f v = 0) {a₁ a₂ : F} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    ∃ y : V ≃ₗ[F] V, y.det = Units.mk0 (a₁ * a₂) (mul_ne_zero ha₁ ha₂) ∧ y v = a₁ • v ∧
      ∀ x, f (y x) = a₂ * f x := by
  obtain ⟨e₁, he₁⟩ := exists_apply_eq_one_of_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hv
  have hr : IsUnit (1 + φ ((a₁ - 1) • v)) := by
    rw [map_smul, hφ, smul_eq_mul, mul_one, add_sub_cancel]
    exact IsUnit.mk0 _ ha₁
  have hs : IsUnit (1 + f ((a₂ - 1) • e₁)) := by
    rw [map_smul, he₁, smul_eq_mul, mul_one, add_sub_cancel]
    exact IsUnit.mk0 _ ha₂
  let r := LinearEquiv.dilatransvection hr
  let s := LinearEquiv.dilatransvection hs
  have hsx : ∀ x, s x = x + f x • ((a₂ - 1) • e₁) := fun x => LinearEquiv.dilatransvection.apply
  have hrx : ∀ x, r x = x + φ x • ((a₁ - 1) • v) := fun x => LinearEquiv.dilatransvection.apply
  have hfs : ∀ x, f (s x) = a₂ * f x := by
    intro x
    rw [hsx, map_add, map_smul, map_smul, he₁, smul_eq_mul, smul_eq_mul, mul_one]
    ring
  refine ⟨s.trans r, ?_, ?_, ?_⟩
  · have hdr : r.det = Units.mk0 a₁ ha₁ := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have := LinearMap.transvection.det φ ((a₁ - 1) • v)
      simp [r, map_smul, hφ]
    have hds : s.det = Units.mk0 a₂ ha₂ := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have := LinearMap.transvection.det f ((a₂ - 1) • e₁)
      simp [s, map_smul, he₁]
    have : (s.trans r).det = r.det * s.det := by
      rw [← LinearEquiv.mul_eq_trans]
      exact map_mul _ _ _
    rw [this, hdr, hds]
    apply Units.ext
    simp
  · show r (s v) = a₁ • v
    rw [hsx, hfv, zero_smul, add_zero, hrx, hφ, one_smul]
    module
  · intro x
    show f (r (s x)) = a₂ * f x
    rw [hrx, map_add, map_smul, map_smul, hfv]
    simp only [smul_zero, add_zero]
    exact hfs x

theorem exists_det_one_conj [FiniteDimensional F V] [Finite F] (hF : ringChar F = 2)
    {f₁ f₂ : Dual F V} {v₁ v₂ : V} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (h₁ : f₁ v₁ = 0) (h₂ : f₂ v₂ = 0) :
    ∃ W : V ≃ₗ[F] V, W.det = 1 ∧ ∀ x, W (x + f₁ x • v₁) = W x + f₂ (W x) • v₂ := by
  obtain ⟨g, c, hc, hgv, hgf⟩ := exists_equiv_flag hf₁ hf₂ hv₁ hv₂ h₁ h₂
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hF ((((g.det : Fˣ) : F)) * c)⁻¹
  have hdc : (((g.det : Fˣ) : F)) * c ≠ 0 := mul_ne_zero g.det.ne_zero hc
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr
    exact inv_ne_zero hdc hr
  obtain ⟨y, hydet, hyv, hyf⟩ := exists_scale_equiv hf₁ hv₁ h₁ (a₁ := c * r) (a₂ := r)
    (mul_ne_zero hc hr0) hr0
  refine ⟨y.trans g, ?_, ?_⟩
  · apply Units.ext
    have h1 : (y.trans g).det = g.det * y.det := by
      rw [← LinearEquiv.mul_eq_trans]
      exact map_mul _ _ _
    rw [h1, hydet, Units.val_mul, Units.val_one, Units.val_mk0]
    have : (((g.det : Fˣ) : F)) * (c * r * r) = (((g.det : Fˣ) : F)) * c * (r * r) := by ring
    rw [this, ← hr, mul_inv_cancel₀ hdc]
  · intro x
    show g (y (x + f₁ x • v₁)) = g (y x) + f₂ (g (y x)) • v₂
    rw [map_add, map_smul, hyv, map_add, map_smul, map_smul, hgv, hgf, hyf, smul_smul]
    rw [show f₁ x * (c * r) = c * (r * f₁ x) by ring]

theorem mem_transvections_of_finrank_fixed [FiniteDimensional F V] [CharP F 2] {e : V ≃ₗ[F] V}
    (he : e * e = 1) (hfix : finrank F V ≤ finrank F e.fixedSubmodule + 1) :
    e ∈ LinearEquiv.transvections F V := by
  rw [LinearEquiv.mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one]
  constructor
  · rw [LinearEquiv.mem_dilatransvections_iff_finrank_quotient]
    have := Submodule.finrank_quotient_add_finrank e.fixedSubmodule
    omega
  · rw [LinearEquiv.one_eq_refl, LinearEquiv.fixedReduce_eq_one]
    intro v
    rw [LinearMap.mem_fixedSubmodule_iff]
    have hee : e (e v) = v := by
      have := congrArg (fun a : V ≃ₗ[F] V => a v) he
      simpa using this
    have h2 : (e v - v) + (e v - v) = 0 := by
      have h20 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
      rw [← two_smul F, h20, zero_smul]
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [neg_sub] at h3
    show e (e v - v) = e v - v
    rw [map_sub, hee]
    exact h3.symm

end Abstract

section Matrix

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def IsTransvection (u : SL(n, F)) : Prop :=
  u ≠ 1 ∧ Matrix.SpecialLinearGroup.toLin' u ∈ LinearEquiv.transvections F (Fin n → F)

theorem ne_zero_of_transvection_ne_one {V : Type*} [AddCommGroup V] [Module F V] {f : Dual F V}
    {v : V} (hfv : f v = 0) (h : LinearEquiv.transvection hfv ≠ 1) : f ≠ 0 ∧ v ≠ 0 := by
  constructor
  · rintro rfl
    exact h (by ext; simp)
  · rintro rfl
    exact h (by ext; simp)

theorem isTransvection_of_card_fixed [Finite F] [CharP F 2] {u : SL(n, F)} (hu : u * u = 1)
    (hu1 : u ≠ 1)
    (hcard : Nat.card {w : Fin n → F // (u : Matrix (Fin n) (Fin n) F) *ᵥ w = w} =
      Nat.card F ^ (n - 1)) : IsTransvection u := by
  refine ⟨hu1, ?_⟩
  set e := Matrix.SpecialLinearGroup.toLin' u with he_def
  have he : e * e = 1 := by rw [he_def, ← map_mul, hu, map_one]
  apply mem_transvections_of_finrank_fixed he
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfix : Nat.card e.fixedSubmodule =
      Nat.card {w : Fin n → F // (u : Matrix (Fin n) (Fin n) F) *ᵥ w = w} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    rw [LinearMap.mem_fixedSubmodule_iff]
    simp [he_def, Matrix.SpecialLinearGroup.toLin'_apply]
  have h1 := Module.natCard_eq_pow_finrank (K := F) (V := e.fixedSubmodule)
  rw [hfix, hcard] at h1
  have h2 := Nat.pow_right_injective hF2 h1
  have hV : finrank F (Fin n → F) = n := by simp
  omega

theorem exists_conj_of_isTransvection [Finite F] [CharP F 2] {u₁ u₂ : SL(n, F)}
    (h₁ : IsTransvection u₁) (h₂ : IsTransvection u₂) : ∃ W : SL(n, F), W * u₁ * W⁻¹ = u₂ := by
  obtain ⟨hu₁, f₁, v₁, hfv₁, he₁⟩ := h₁
  obtain ⟨hu₂, f₂, v₂, hfv₂, he₂⟩ := h₂
  have hne₁ : LinearEquiv.transvection hfv₁ ≠ 1 := by
    rw [← he₁]
    intro h
    apply hu₁
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [h, map_one]
  have hne₂ : LinearEquiv.transvection hfv₂ ≠ 1 := by
    rw [← he₂]
    intro h
    apply hu₂
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [h, map_one]
  obtain ⟨hf₁, hv₁⟩ := ne_zero_of_transvection_ne_one hfv₁ hne₁
  obtain ⟨hf₂, hv₂⟩ := ne_zero_of_transvection_ne_one hfv₂ hne₂
  obtain ⟨W', hdet, hW'⟩ := exists_det_one_conj (ringChar.eq F 2) hf₁ hf₂ hv₁ hv₂ hfv₁ hfv₂
  refine ⟨(Matrix.SpecialLinearGroup.toLin'_equiv).symm ⟨W', hdet⟩, ?_⟩
  apply Matrix.SpecialLinearGroup.toLin'_injective
  have hW : Matrix.SpecialLinearGroup.toLin'
      ((Matrix.SpecialLinearGroup.toLin'_equiv).symm ⟨W', hdet⟩) = W' := by
    have := (Matrix.SpecialLinearGroup.toLin'_equiv).apply_symm_apply ⟨W', hdet⟩
    exact congrArg Subtype.val this
  rw [map_mul, map_mul, map_inv, hW, he₁, he₂, mul_inv_eq_iff_eq_mul]
  refine LinearEquiv.ext fun x => ?_
  exact hW' x

end Matrix

end CFSG.CGT.Timmesfeld75
