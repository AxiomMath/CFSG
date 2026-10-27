module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Coordinates

variable {F : Type} [Field F]

theorem translation_one_mul_self [CharP F 2] :
    translation F 1 * translation F 1 = 1 := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some y =>
    simp only [Equiv.Perm.mul_apply, translation_some, Equiv.Perm.one_apply, Option.some.injEq]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem inversion_mul_self' : inversion F * inversion F = 1 := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => simp
  | some y =>
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy' : -y⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hy)
      simp [Equiv.Perm.mul_apply, inversion_nonzero F y hy, inversion_nonzero F _ hy', inv_neg,
        inv_inv]

theorem fieldExtension_comm_translation_one (σ : F ≃+* F) :
    fieldExtension F σ * translation F 1 = translation F 1 * fieldExtension F σ := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some y => simp only [Equiv.Perm.mul_apply, translation_some, fieldExtension_some, map_add, map_one]

theorem fieldExtension_comm_inversion (σ : F ≃+* F) :
    fieldExtension F σ * inversion F = inversion F * fieldExtension F σ := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none =>
    simp only [Equiv.Perm.mul_apply, inversion_none, fieldExtension_none, fieldExtension_some,
      map_zero]
  | some y =>
    by_cases hy : y = 0
    · subst hy
      simp only [Equiv.Perm.mul_apply, inversion_zero, fieldExtension_none, fieldExtension_some,
        map_zero]
    · have hσy : σ y ≠ 0 := (map_ne_zero σ).2 hy
      simp only [Equiv.Perm.mul_apply, inversion_nonzero F y hy, inversion_nonzero F (σ y) hσy,
        fieldExtension_some, map_neg, map_inv₀]

theorem translation_one_mul_inversion_ne :
    translation F 1 * inversion F ≠ inversion F * translation F 1 := by
  intro h
  have := congrArg (fun g : Equiv.Perm (Omega F) => g none) h
  simp only [Equiv.Perm.mul_apply, inversion_none, translation_some, translation_none] at this
  have h01 : (0 : F) + 1 = 0 := Option.some.inj this
  rw [zero_add] at h01
  exact one_ne_zero h01

end Coordinates

section Conjugation

variable {G : Type*} [Group G]

theorem conj_mul_conj_mul_inv_of_comm {h s x : G} (hsx : s * x = x * s) :
    (h * s * h⁻¹) * (h * x * h⁻¹) * (h * s * h⁻¹)⁻¹ = h * x * h⁻¹ := by
  calc (h * s * h⁻¹) * (h * x * h⁻¹) * (h * s * h⁻¹)⁻¹ = h * (s * x * s⁻¹) * h⁻¹ := by group
    _ = h * x * h⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hsx]

theorem conj_mul_self_eq_one {h x : G} (hx : x * x = 1) : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := by
  calc (h * x * h⁻¹) * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
    _ = 1 := by rw [hx]; group

theorem conj_mul_ne_conj_mul {h x y : G} (hxy : x * y ≠ y * x) :
    (h * x * h⁻¹) * (h * y * h⁻¹) ≠ (h * y * h⁻¹) * (h * x * h⁻¹) := by
  intro hcomm
  apply hxy
  have e1 : (h * x * h⁻¹) * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
  have e2 : (h * y * h⁻¹) * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
  rw [e1, e2] at hcomm
  simpa using hcomm

end Conjugation

section Main

open CFSG.BenderSuzuki

theorem exists_normal_form_outer_involution_coordinateG {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (α : MulAut (coordinateG F)) (hα : α * α = 1)
    (hout : ¬ ∃ g : coordinateG F, ∀ x : coordinateG F, α x = g * x * g⁻¹) :
    Even n ∧ ∃ (a : coordinateE F) (σ : F ≃+* F) (h₀ : Equiv.Perm (Omega F)),
      (∀ g : coordinateG F, ((α g : coordinateG F) : Equiv.Perm (Omega F)) =
        (a : Equiv.Perm (Omega F)) * g * (a : Equiv.Perm (Omega F))⁻¹) ∧
      h₀ ∈ coordinateG F ∧ (a : Equiv.Perm (Omega F)) = h₀ * fieldExtension F σ * h₀⁻¹ ∧
      σ ≠ 1 ∧ σ * σ = 1 ∧ (∀ x, σ x = x ^ 2 ^ (n / 2)) ∧
      ∃ k : Subfield F, (k : Set F) = {x | σ x = x} ∧ Nat.card k = 2 ^ (n / 2) := by
  obtain ⟨c, hc, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism F
  obtain ⟨a, hca⟩ : ∃ a : coordinateE F, c a = α := ⟨c.symm α, c.apply_symm_apply α⟩
  have haa : a * a = 1 := by
    apply c.injective
    rw [map_mul, hca, map_one, hα]
  have haa' : (a : Equiv.Perm (Omega F)) * (a : Equiv.Perm (Omega F)) = 1 :=
    congrArg Subtype.val haa
  have hα_apply : ∀ g : coordinateG F, ((α g : coordinateG F) : Equiv.Perm (Omega F)) =
      (a : Equiv.Perm (Omega F)) * g * (a : Equiv.Perm (Omega F))⁻¹ := by
    intro g
    rw [← hca]
    exact hc a g
  have ha1 : (a : Equiv.Perm (Omega F)) ≠ 1 := by
    intro h1
    apply hout
    refine ⟨1, fun x => ?_⟩
    apply Subtype.ext
    rw [hα_apply, h1]
    simp
  have hord : orderOf (a : Equiv.Perm (Omega F)) = 2 := by
    apply orderOf_eq_prime _ ha1
    rw [sq]
    exact haa'
  obtain ⟨-, -, -, -, -, -, -, -, -, hnf⟩ := even_linear_two_involution_normal_forms hn hF
  rcases hnf (a : Equiv.Perm (Omega F)) a.2 hord with
    ⟨haG, -⟩ | ⟨-, hEven, σ, hσ1, hσσ, hσpow, -, -, ⟨h₀, hh₀, hah₀⟩, hk⟩
  ·
    exfalso
    apply hout
    set g₀ : coordinateG F := ⟨(a : Equiv.Perm (Omega F)), haG⟩ with hg₀
    have hae : a = ⟨g₀, ((coordinateG_le_D F).trans (coordinateD_le_E F)) g₀.property⟩ :=
      Subtype.ext rfl
    have hαconj : α = MulAut.conj g₀ := by rw [← hca, hae, hcG g₀]
    exact ⟨g₀, fun x => by rw [hαconj]; rfl⟩
  · exact ⟨hEven, a, σ, h₀, hα_apply, hh₀, hah₀, hσ1, hσσ, hσpow, hk⟩

theorem exists_fixed_noncommuting_involutions_coordinateG {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (α : MulAut (coordinateG F)) (hα : α * α = 1)
    (hout : ¬ ∃ g : coordinateG F, ∀ x : coordinateG F, α x = g * x * g⁻¹) :
    ∃ y₁ y₂ : coordinateG F, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ α y₁ = y₁ ∧ α y₂ = y₂ ∧
      y₁ * y₂ ≠ y₂ * y₁ := by
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  obtain ⟨-, a, σ, h₀, hα_apply, hh₀, hah₀, -⟩ :=
    exists_normal_form_outer_involution_coordinateG hn hF α hα hout
  have hu : translation F 1 ∈ coordinateG F := translation_mem_coordinateG F 1
  have hι : inversion F ∈ coordinateG F := inversion_mem_coordinateG F
  have hg₁ : h₀ * translation F 1 * h₀⁻¹ ∈ coordinateG F :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₀ hu) (Subgroup.inv_mem _ hh₀)
  have hg₂ : h₀ * inversion F * h₀⁻¹ ∈ coordinateG F :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₀ hι) (Subgroup.inv_mem _ hh₀)
  refine ⟨⟨_, hg₁⟩, ⟨_, hg₂⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (conj_mul_self_eq_one (translation_one_mul_self))
  · exact Subtype.ext (conj_mul_self_eq_one (inversion_mul_self'))
  · apply Subtype.ext
    rw [hα_apply, hah₀]
    exact conj_mul_conj_mul_inv_of_comm (fieldExtension_comm_translation_one σ)
  · apply Subtype.ext
    rw [hα_apply, hah₀]
    exact conj_mul_conj_mul_inv_of_comm (fieldExtension_comm_inversion σ)
  · intro hcomm
    exact conj_mul_ne_conj_mul translation_one_mul_inversion_ne (congrArg Subtype.val hcomm)

theorem BenderType.exists_fixed_noncommuting_involutions_linear {K : Type*} [Group K] {n : ℕ}
    (h : BenderType K n 1 1) (α : MulAut K) (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    ∃ y₁ y₂ : K, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ α y₁ = y₁ ∧ α y₂ = y₂ ∧ y₁ * y₂ ≠ y₂ * y₁ := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let θ : K ≃* coordinateG (GaloisField 2 n) := e.trans (pslEquivCoordinateG (GaloisField 2 n))
  have hα'_apply : ∀ y, MulAut.congr θ α y = θ (α (θ.symm y)) := fun y => rfl
  have hα'α' : MulAut.congr θ α * MulAut.congr θ α = 1 := by
    rw [← map_mul, hα, map_one]
  have hout' : ¬ ∃ g : coordinateG (GaloisField 2 n), ∀ x, MulAut.congr θ α x = g * x * g⁻¹ := by
    rintro ⟨g, hg⟩
    apply hout
    refine ⟨θ.symm g, fun x => ?_⟩
    have := hg (θ x)
    rw [hα'_apply, MulEquiv.symm_apply_apply] at this
    apply θ.injective
    rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨y₁, y₂, h₁, h₂, hf₁, hf₂, hne⟩ :=
    exists_fixed_noncommuting_involutions_coordinateG (by omega) hcard (MulAut.congr θ α) hα'α'
      hout'
  refine ⟨θ.symm y₁, θ.symm y₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h₁, map_one]
  · rw [← map_mul, h₂, map_one]
  · apply θ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hf₁
  · apply θ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hf₂
  · intro hcomm
    apply hne
    apply θ.symm.injective
    rw [map_mul, map_mul]
    exact hcomm

end Main

section Final

theorem BenderType.outer_involution_of_fixed_noncommuting
    {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) (α : MulAut K)
    (hfix : ∃ y₁ y₂ : K, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ α y₁ = y₁ ∧ α y₂ = y₂ ∧
      y₁ * y₂ ≠ y₂ * y₁) :
    (∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y) ∧
      ∀ S : Sylow 2 K, ∃ x : K, α x = x ∧ x ∉ normalizer ((S : Subgroup K) : Set K) := by
  obtain ⟨y₁, y₂, h₁, h₂, hf₁, hf₂, hne⟩ := hfix
  have hy₁ : y₁ ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hy₂ : y₂ ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  refine ⟨⟨y₁, hy₁, h₁, hf₁⟩, fun S => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  have hord : ∀ {y : K}, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun {y} hy hy1 => by
    apply orderOf_eq_prime _ hy1
    rw [sq]
    exact hy
  have hz₁ : y₁ ∈ rootCenter (S : Subgroup K) :=
    (hc.involution_iff.mp ⟨hcon y₁ hf₁, hord h₁ hy₁⟩).1
  have hz₂ : y₂ ∈ rootCenter (S : Subgroup K) :=
    (hc.involution_iff.mp ⟨hcon y₂ hf₂, hord h₂ hy₂⟩).1
  exact hne ((mem_rootCenter_iff.mp hz₁).2 y₂ (rootCenter_le _ hz₂)).symm

theorem BenderType.outer_involution_linear
    {K : Type*} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 1 1) (α : MulAut K) (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    (∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y) ∧
      ∀ S : Sylow 2 K, ∃ x : K, α x = x ∧ x ∉ normalizer ((S : Subgroup K) : Set K) :=
  h.outer_involution_of_fixed_noncommuting α
    (h.exists_fixed_noncommuting_involutions_linear α hα hout)

end Final

end CFSG.GH74.Uniqueness.Bender
