module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.HardMathSupport.U4FF.BOAlt
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.U4FF

open Module QuadraticMap

section Core

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

@[expose] def fixSub (Φ : AddSubgroup (Module.End F V)) : Submodule F V where
  carrier := {x | ∀ φ ∈ Φ, φ x = 0}
  add_mem' := fun {x y} hx hy φ hφ => by rw [map_add, hx φ hφ, hy φ hφ, add_zero]
  zero_mem' := fun φ _ => map_zero φ
  smul_mem' := fun c {x} hx φ hφ => by rw [map_smul, hx φ hφ, smul_zero]

theorem mem_fixSub {Φ : AddSubgroup (Module.End F V)} {x : V} :
    x ∈ fixSub Φ ↔ ∀ φ ∈ Φ, φ x = 0 := Iff.rfl

@[expose] def imgSub (Φ : AddSubgroup (Module.End F V)) : Submodule F V :=
  Submodule.span F {w | ∃ φ ∈ Φ, ∃ x, w = φ x}

theorem mem_imgSub_of {Φ : AddSubgroup (Module.End F V)} {φ : Module.End F V} (hφ : φ ∈ Φ)
    (x : V) : φ x ∈ imgSub Φ :=
  Submodule.subset_span ⟨φ, hφ, x, rfl⟩

variable (qf : QuadraticForm F V) {Φ : AddSubgroup (Module.End F V)}

theorem polar_isometry_id (hiso : ∀ φ ∈ Φ, ∀ x, qf (x + φ x) = qf x) {φ : Module.End F V}
    (hφ : φ ∈ Φ) (x y : V) :
    polar qf x (φ y) + polar qf (φ x) y + polar qf (φ x) (φ y) = 0 := by
  have h1 := hiso φ hφ (x + y)
  rw [map_add φ x y] at h1
  have e1 : x + y + (φ x + φ y) = (x + φ x) + (y + φ y) := by abel
  rw [e1, QuadraticMap.map_add qf (x + φ x) (y + φ y), hiso φ hφ x, hiso φ hφ y,
    QuadraticMap.map_add qf x y] at h1
  have e2 : polar qf (x + φ x) (y + φ y) = polar qf x y + polar qf x (φ y) +
      polar qf (φ x) y + polar qf (φ x) (φ y) := by
    rw [polar_add_left, polar_add_right, polar_add_right]
    ring
  rw [e2] at h1
  linear_combination h1

theorem qf_img_eq (hiso : ∀ φ ∈ Φ, ∀ x, qf (x + φ x) = qf x) {φ : Module.End F V} (hφ : φ ∈ Φ)
    (x : V) : qf (φ x) = polar qf x (φ x) := by
  have h1 := hiso φ hφ x
  rw [QuadraticMap.map_add qf x (φ x)] at h1
  have : qf (φ x) + polar qf x (φ x) = 0 := by linear_combination h1
  have h2 := CharTwo.add_eq_zero.mp this
  exact h2

section Struct

variable {qf} (hnd : (polarBilin qf).Nondegenerate)
  (hsq : ∀ φ ∈ Φ, ∀ ψ ∈ Φ, ∀ x, φ (ψ x) = 0)
  (hiso : ∀ φ ∈ Φ, ∀ x, qf (x + φ x) = qf x)

include hnd in
theorem polar_left_zero {x : V} (h : ∀ y, polar qf x y = 0) : x = 0 :=
  hnd.1 x (fun y => by rw [polarBilin_apply_apply]; exact h y)

include hnd in
theorem polar_right_zero {z : V} (h : ∀ x, polar qf x z = 0) : z = 0 :=
  polar_left_zero hnd (fun x => by rw [polar_comm]; exact h x)

include hsq in
theorem imgSub_le_fixSub : imgSub Φ ≤ fixSub Φ := by
  refine Submodule.span_le.mpr ?_
  rintro w ⟨ψ, hψ, x, rfl⟩
  rw [SetLike.mem_coe, mem_fixSub]
  intro φ hφ
  exact hsq φ hφ ψ hψ x

include hiso in
theorem polar_img_fix {w y : V} (hw : w ∈ imgSub Φ) (hy : y ∈ fixSub Φ) : polar qf w y = 0 := by
  unfold imgSub at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨φ, hφ, x, rfl⟩ := hw
    have h := polar_isometry_id qf hiso hφ x y
    rw [mem_fixSub.mp hy φ hφ, polar_zero_right, polar_zero_right] at h
    simpa using h
  | zero => exact polar_zero_left qf y
  | add w w' _ _ h1 h2 => rw [polar_add_left, h1, h2, add_zero]
  | smul c w _ h1 => rw [polar_smul_left, h1, smul_zero]

include hsq hiso in
theorem polar_img_img {w w' : V} (hw : w ∈ imgSub Φ) (hw' : w' ∈ imgSub Φ) :
    polar qf w w' = 0 :=
  polar_img_fix hiso hw (imgSub_le_fixSub hsq hw')

include hnd hsq hiso in
theorem mem_fixSub_of_perp {y : V} (hy : ∀ w ∈ imgSub Φ, polar qf w y = 0) : y ∈ fixSub Φ := by
  intro φ hφ
  apply polar_right_zero hnd
  intro x
  have h := polar_isometry_id qf hiso hφ x y
  rw [hy _ (mem_imgSub_of hφ x), polar_img_img hsq hiso (mem_imgSub_of hφ x)
    (mem_imgSub_of hφ y), add_zero, add_zero] at h
  exact h

include hnd hsq hiso in
theorem orthogonal_imgSub_eq :
    LinearMap.BilinForm.orthogonal (polarBilin qf) (imgSub Φ) = fixSub Φ := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact mem_fixSub_of_perp hnd hsq hiso (fun w hw => by
      have := h w hw
      rwa [polarBilin_apply_apply] at this)
  · intro hy w hw
    rw [polarBilin_apply_apply]
    exact polar_img_fix hiso hw hy

include hnd hsq hiso in
theorem finrank_imgSub_add_fixSub :
    finrank F (imgSub Φ) + finrank F (fixSub Φ) = finrank F V := by
  have h := LinearMap.BilinForm.finrank_orthogonal hnd (imgSub Φ)
  rw [orthogonal_imgSub_eq hnd hsq hiso] at h
  have hle : finrank F (imgSub Φ) ≤ finrank F V := Submodule.finrank_le _
  omega

end Struct

section Count

variable {qf} (hnd : (polarBilin qf).Nondegenerate)
  (hsq : ∀ φ ∈ Φ, ∀ ψ ∈ Φ, ∀ x, φ (ψ x) = 0)
  (hiso : ∀ φ ∈ Φ, ∀ x, qf (x + φ x) = qf x)

include hnd hsq hiso in
theorem exists_sqrt_functional : ∃ y₁ : V, ∀ u ∈ imgSub Φ, qf u = (polar qf u y₁) ^ 2 := by
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  have hbij : Function.Bijective (frobenius F 2) :=
    ⟨frobenius_inj F 2, Finite.injective_iff_surjective.mp (frobenius_inj F 2)⟩
  let fr : F ≃+* F := RingEquiv.ofBijective (frobenius F 2) hbij
  have hfr : ∀ a, fr a = a ^ 2 := fun a => rfl
  let lam : (imgSub Φ) →ₗ[F] F :=
    { toFun := fun u => fr.symm (qf u)
      map_add' := fun u u' => by
        have h := QuadraticMap.map_add qf (u : V) u'
        rw [polar_img_img hsq hiso u.2 u'.2, add_zero] at h
        show fr.symm (qf ((u : V) + u')) = _
        rw [h, map_add]
      map_smul' := fun c u => by
        show fr.symm (qf (c • (u : V))) = c • fr.symm (qf u)
        rw [QuadraticMap.map_smul, smul_eq_mul, map_mul]
        have : fr.symm (c * c) = c := by
          rw [← _root_.sq, ← hfr c, RingEquiv.symm_apply_apply]
        rw [this, smul_eq_mul] }
  obtain ⟨ω, hω⟩ := LinearMap.exists_extend lam
  refine ⟨(LinearMap.BilinForm.toDual (polarBilin qf) hnd).symm ω, fun u hu => ?_⟩
  have h1 : polar qf ((LinearMap.BilinForm.toDual (polarBilin qf) hnd).symm ω) u = ω u := by
    have := LinearMap.BilinForm.apply_toDual_symm_apply (B := polarBilin qf) (hB := hnd)
      (f := ω) (v := u)
    rwa [polarBilin_apply_apply] at this
  have h2 : ω u = fr.symm (qf u) := by
    have := congrArg (fun L : imgSub Φ →ₗ[F] F => L ⟨u, hu⟩) hω
    exact this
  rw [polar_comm, h1, h2, ← hfr, RingEquiv.apply_symm_apply]

include hnd hsq hiso in
theorem quad_count_params (hdim : finrank F V = 6) :
    ∃ r : ℕ, r ≤ 3 ∧ Nat.card (fixSub Φ) = Nat.card F ^ (6 - r) ∧
      Nat.card Φ ≤ 2 * Nat.card F ^ (r * (r - 1) / 2) := by
  classical
  obtain ⟨y₁, hy₁⟩ := exists_sqrt_functional hnd hsq hiso
  have hCD := finrank_imgSub_add_fixSub hnd hsq hiso
  have hDC : finrank F (imgSub Φ) ≤ finrank F (fixSub Φ) :=
    Submodule.finrank_mono (imgSub_le_fixSub hsq)
  set r := finrank F (imgSub Φ) with hr
  have hr3 : r ≤ 3 := by omega
  have hCr : finrank F (fixSub Φ) = 6 - r := by omega
  refine ⟨r, hr3, ?_, ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := F) (V := fixSub Φ), hCr]
  obtain ⟨X, hX⟩ := Submodule.exists_isCompl (fixSub Φ)
  have hXr : finrank F X = r := by
    have := Submodule.finrank_add_eq_of_isCompl hX
    omega
  have hdecomp : ∀ v : V, ∃ c ∈ fixSub Φ, ∃ u ∈ X, v = c + u := fun v => by
    have : v ∈ fixSub Φ ⊔ X := by rw [hX.sup_eq_top]; trivial
    obtain ⟨c, hc, u, hu, h⟩ := Submodule.mem_sup.mp this
    exact ⟨c, hc, u, hu, h.symm⟩
  obtain ⟨c₁, hc₁, x₁, hx₁, hy₁dec⟩ := hdecomp y₁
  let Ξ : Φ →+ F := AddMonoidHom.mk' (fun φ => polar qf ((φ : Module.End F V) y₁) y₁)
    (fun φ ψ => by
      simp only [AddSubgroup.coe_add, LinearMap.add_apply, polar_add_left])
  have hΞ : ∀ φ : Φ, Ξ φ = (Ξ φ) ^ 2 := fun φ => by
    have h1 : qf ((φ : Module.End F V) y₁) = polar qf y₁ ((φ : Module.End F V) y₁) :=
      qf_img_eq qf hiso φ.2 y₁
    have h2 := hy₁ _ (mem_imgSub_of φ.2 y₁)
    show polar qf ((φ : Module.End F V) y₁) y₁ = (polar qf ((φ : Module.End F V) y₁) y₁) ^ 2
    rw [← h2, h1, polar_comm]
  have hmain := AddSubgroup.card_ker_mul_card_range Ξ
  have hrange : Nat.card Ξ.range ≤ 2 := by
    have key : ∀ a : Ξ.range, (a : F) = 0 ∨ (a : F) = 1 := by
      rintro ⟨_, φ, rfl⟩
      have h := hΞ φ
      have h' : Ξ φ * (Ξ φ - 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h' with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    have hinj : Function.Injective (fun a : Ξ.range => decide ((a : F) = 0)) := by
      intro a b hab
      apply Subtype.ext
      have hab' : ((a : F) = 0) ↔ ((b : F) = 0) := by simpa using hab
      rcases key a with ha | ha <;> rcases key b with hb | hb
      · rw [ha, hb]
      · exfalso
        have := hab'.mp ha
        rw [hb] at this
        exact one_ne_zero this
      · exfalso
        have := hab'.mpr hb
        rw [ha] at this
        exact one_ne_zero this
      · rw [ha, hb]
    calc Nat.card Ξ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hker : Nat.card Ξ.ker ≤ Nat.card F ^ (r * (r - 1) / 2) := by
    let x₁' : X := ⟨x₁, hx₁⟩
    let ℓ : Φ → (X →ₗ[F] F) := fun φ =>
      (LinearMap.flip (polarBilin qf) y₁) ∘ₗ (φ : Module.End F V) ∘ₗ X.subtype
    let γ : Φ → LinearMap.BilinForm F X := fun φ =>
      (polarBilin qf).compl₁₂ ((φ : Module.End F V) ∘ₗ X.subtype) X.subtype +
        (LinearMap.lsmul F F).compl₁₂ (ℓ φ) (ℓ φ)
    have hγ : ∀ φ u u', γ φ u u' = polar qf ((φ : Module.End F V) (u : V)) (u' : V) +
        polar qf ((φ : Module.End F V) (u : V)) y₁ *
          polar qf ((φ : Module.End F V) (u' : V)) y₁ := by
      intro φ u u'
      simp [γ, ℓ, polarBilin_apply_apply, LinearMap.flip_apply, LinearMap.lsmul_apply]
    have halt : ∀ (φ : Φ) (u : X), γ φ u u = 0 := fun φ u => by
      have h1 : polar qf ((φ : Module.End F V) (u : V)) (u : V) =
          qf ((φ : Module.End F V) (u : V)) := by
        rw [polar_comm, ← qf_img_eq qf hiso φ.2 u]
      have h2 : qf ((φ : Module.End F V) (u : V)) =
          polar qf ((φ : Module.End F V) (u : V)) y₁ ^ 2 := hy₁ _ (mem_imgSub_of φ.2 _)
      rw [hγ, h1, h2, ← _root_.sq]
      exact CharTwo.add_self_eq_zero _
    let Γ : Ξ.ker → {β : LinearMap.BilinForm F X // ∀ x, β x x = 0} :=
      fun φ => ⟨γ φ.1, halt φ.1⟩
    have hΓ : Function.Injective Γ := by
      intro φ ψ hφψ
      have hγeq : γ φ.1 = γ ψ.1 := congrArg Subtype.val hφψ
      have hker0 : ∀ χ : Ξ.ker, polar qf ((χ.1 : Module.End F V) x₁) y₁ = 0 := by
        intro χ
        have h0 : Ξ χ.1 = 0 := χ.2
        have h1 : (χ.1 : Module.End F V) y₁ = (χ.1 : Module.End F V) x₁ := by
          rw [hy₁dec, map_add, mem_fixSub.mp hc₁ _ χ.1.2, zero_add]
        have : polar qf ((χ.1 : Module.End F V) y₁) y₁ = 0 := h0
        rwa [h1] at this
      have hlin : ∀ (χ : Ξ.ker) (u : X), polar qf ((χ.1 : Module.End F V) (u : V)) y₁ =
          γ χ.1 u x₁' := by
        intro χ u
        have h := hγ χ.1 u x₁'
        have h4 : polar qf ((χ.1 : Module.End F V) (x₁' : V)) y₁ = 0 := hker0 χ
        have h3 : polar qf ((χ.1 : Module.End F V) (u : V)) y₁ =
            polar qf ((χ.1 : Module.End F V) (u : V)) (x₁' : V) := by
          rw [hy₁dec, polar_add_right, polar_img_fix hiso (mem_imgSub_of χ.1.2 _) hc₁, zero_add]
        rw [h4, mul_zero, add_zero] at h
        rw [h3, h]
      have hpol : ∀ (χ : Ξ.ker) (u u' : X),
          polar qf ((χ.1 : Module.End F V) (u : V)) (u' : V) =
            γ χ.1 u u' - γ χ.1 u x₁' * γ χ.1 u' x₁' := by
        intro χ u u'
        have h := hγ χ.1 u u'
        rw [hlin χ u, hlin χ u'] at h
        linear_combination (-1 : F) * h
      have hXX : ∀ u u' : X, polar qf ((φ.1 : Module.End F V) (u : V)) (u' : V) =
          polar qf ((ψ.1 : Module.End F V) (u : V)) (u' : V) := by
        intro u u'
        rw [hpol φ, hpol ψ, hγeq]
      have hVV : ∀ x x' : V, polar qf ((φ.1 : Module.End F V) x) x' =
          polar qf ((ψ.1 : Module.End F V) x) x' := by
        intro x x'
        obtain ⟨c, hc, u, hu, rfl⟩ := hdecomp x
        obtain ⟨c', hc', u', hu', rfl⟩ := hdecomp x'
        have e1 : ∀ χ : Ξ.ker, polar qf ((χ.1 : Module.End F V) (c + u)) (c' + u') =
            polar qf ((χ.1 : Module.End F V) u) u' := by
          intro χ
          rw [map_add, mem_fixSub.mp hc _ χ.1.2, zero_add, polar_add_right,
            polar_img_fix hiso (mem_imgSub_of χ.1.2 _) hc', zero_add]
        rw [e1 φ, e1 ψ]
        exact hXX ⟨u, hu⟩ ⟨u', hu'⟩
      have hφψ' : (φ.1 : Module.End F V) = (ψ.1 : Module.End F V) := LinearMap.ext fun x => by
        have : ((φ.1 : Module.End F V) x - (ψ.1 : Module.End F V) x) = 0 :=
          polar_left_zero hnd (fun x' => by rw [polar_sub_left, hVV x x', sub_self])
        exact sub_eq_zero.mp this
      exact Subtype.ext (Subtype.ext hφψ')
    haveI : Finite (LinearMap.BilinForm F X) := Module.finite_of_finite F
    have hcard := card_alternating_le (F := F) (X := X) (by rw [hXr]; exact hr3)
    rw [hXr] at hcard
    exact (Nat.card_le_card_of_injective Γ hΓ).trans hcard
  calc Nat.card Φ = Nat.card Ξ.ker * Nat.card Ξ.range := hmain.symm
    _ ≤ Nat.card F ^ (r * (r - 1) / 2) * 2 := Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card F ^ (r * (r - 1) / 2) := mul_comm _ _

end Count

end Core

end CFSG.HardMathSupport.U4FF
