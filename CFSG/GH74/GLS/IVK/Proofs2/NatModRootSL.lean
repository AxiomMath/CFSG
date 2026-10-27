module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModDefs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix
open scoped commutatorElement

namespace RootSL

variable {G : Type*} [Group G]

theorem commutatorElement_mul_right_of_commute {a u v : G}
    (h₁ : Commute u ⁅a, v⁆) : ⁅a, u * v⁆ = ⁅a, u⁆ * ⁅a, v⁆ := by
  simp only [commutatorElement_def]
  have h := h₁.eq
  simp only [commutatorElement_def] at h
  calc a * (u * v) * a⁻¹ * (u * v)⁻¹ = a * u * a⁻¹ * u⁻¹ * (u * (a * v * a⁻¹ * v⁻¹) * u⁻¹) := by
        group
    _ = a * u * a⁻¹ * u⁻¹ * (a * v * a⁻¹ * v⁻¹) := by
        rw [h]
        group

theorem commutatorElement_mul_left' (a b v : G) :
    ⁅a * b, v⁆ = a * ⁅b, v⁆ * a⁻¹ * ⁅a, v⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_commutatorElement_mul (a u : G) : a * u * a⁻¹ = ⁅a, u⁆ * u := by
  simp only [commutatorElement_def]
  group

end RootSL

section Module

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable (π : SpecialLinearGroup (Fin 2) F →* G) (V₁ V₂ : Subgroup G)

structure IsRootModuleSL : Prop where
  comm₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a
  comm₂ : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a
  comm₁₂ : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a
  inter : ∀ a ∈ V₁, a ∈ V₂ → a = 1
  card₁ : Nat.card V₁ = Nat.card F
  card₂ : Nat.card V₂ = Nat.card F
  up₁ : ∀ (c : F), ∀ v ∈ V₁, π (upperSL c) * v = v * π (upperSL c)
  up₂ : ∀ (c : F), ∀ v ∈ V₂, ⁅π (upperSL c), v⁆ ∈ V₁
  low₂ : ∀ (c : F), ∀ v ∈ V₂, π (lowerSL c) * v = v * π (lowerSL c)
  low₁ : ∀ (c : F), ∀ v ∈ V₁, ⁅π (lowerSL c), v⁆ ∈ V₂
  nondeg : ∀ v ∈ V₂, (∀ c : F, π (upperSL c) * v = v * π (upperSL c)) → v = 1

variable {π V₁ V₂}

namespace IsRootModuleSL

variable (hV : IsRootModuleSL π V₁ V₂)
include hV

@[expose] def lam (c : F) : V₂ →* V₁ where
  toFun v := ⟨⁅π (upperSL c), (v : G)⁆, hV.up₂ c v v.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    apply RootSL.commutatorElement_mul_right_of_commute
    exact (hV.comm₁₂ _ (hV.up₂ c v v.2) _ u.2).symm

theorem lam_coe (c : F) (v : V₂) : (hV.lam c v : G) = ⁅π (upperSL c), (v : G)⁆ := rfl

@[expose] def mu (d : F) : V₁ →* V₂ where
  toFun v := ⟨⁅π (lowerSL d), (v : G)⁆, hV.low₁ d v v.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    apply RootSL.commutatorElement_mul_right_of_commute
    exact hV.comm₁₂ _ u.2 _ (hV.low₁ d v v.2)

theorem mu_coe (d : F) (v : V₁) : (hV.mu d v : G) = ⁅π (lowerSL d), (v : G)⁆ := rfl

theorem lam_add (c c' : F) (v : V₂) : hV.lam (c + c') v = hV.lam c v * hV.lam c' v := by
  apply Subtype.ext
  simp only [lam_coe, Subgroup.coe_mul]
  rw [← upperSL_add, map_mul, RootSL.commutatorElement_mul_left']
  have h := hV.up₁ c _ (hV.up₂ c' v v.2)
  rw [h, mul_inv_cancel_right]
  exact hV.comm₁ _ (hV.up₂ c' v v.2) _ (hV.up₂ c v v.2)

theorem mu_add (d d' : F) (v : V₁) : hV.mu (d + d') v = hV.mu d v * hV.mu d' v := by
  apply Subtype.ext
  simp only [mu_coe, Subgroup.coe_mul]
  rw [← lowerSL_add, map_mul, RootSL.commutatorElement_mul_left']
  have h := hV.low₂ d _ (hV.low₁ d' v v.2)
  rw [h, mul_inv_cancel_right]
  exact hV.comm₂ _ (hV.low₁ d' v v.2) _ (hV.low₁ d v v.2)

theorem lam_zero (v : V₂) : hV.lam 0 v = 1 := by
  apply Subtype.ext
  simp [lam_coe, upperSL_zero]

theorem mu_zero (v : V₁) : hV.mu 0 v = 1 := by
  apply Subtype.ext
  simp [mu_coe, lowerSL_zero]

theorem mu_neg (d : F) (v : V₁) : hV.mu (-d) v = (hV.mu d v)⁻¹ := by
  have h := hV.mu_add (-d) d v
  rw [neg_add_cancel, hV.mu_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem up_conj (c : F) (u : V₂) :
    π (upperSL c) * u * (π (upperSL c))⁻¹ = (hV.lam c u : G) * u := by
  rw [lam_coe, RootSL.conj_eq_commutatorElement_mul]

theorem low_conj (d : F) (v : V₁) :
    π (lowerSL d) * v * (π (lowerSL d))⁻¹ = (hV.mu d v : G) * v := by
  rw [mu_coe, RootSL.conj_eq_commutatorElement_mul]

theorem eq_one_of_commute_upper {v₁ v₂ : G} (h₁ : v₁ ∈ V₁) (h₂ : v₂ ∈ V₂)
    (h : ∀ c : F, π (upperSL c) * (v₁ * v₂) = v₁ * v₂ * π (upperSL c)) : v₂ = 1 := by
  apply hV.nondeg v₂ h₂
  intro c
  have hc := h c
  have hv₁ := hV.up₁ c v₁ h₁
  rw [← mul_assoc, hv₁, mul_assoc, mul_assoc] at hc
  exact mul_left_cancel hc

theorem weyl_conj (a : Fˣ) (u : V₂) :
    π (weylSL a) * u * (π (weylSL a))⁻¹ = hV.lam a u ∧ hV.mu ((a⁻¹ : Fˣ) : F) (hV.lam a u) = u := by
  set ℓ : V₁ := hV.lam a u with hℓ
  set m : V₂ := hV.mu (-((a⁻¹ : Fˣ) : F)) ℓ with hm
  have hexp : π (weylSL a) * u * (π (weylSL a))⁻¹ =
      ((hV.lam a m : G) * ℓ * hV.lam a u) * ((m : G) * u) := by
    rw [weylSL_eq, map_mul, map_mul]
    have e1 : π (upperSL (a : F)) * u * (π (upperSL (a : F)))⁻¹ = (ℓ : G) * u := hV.up_conj _ u
    have e2 : π (lowerSL (-((a⁻¹ : Fˣ) : F))) * ((ℓ : G) * u) *
        (π (lowerSL (-((a⁻¹ : Fˣ) : F))))⁻¹ = (m : G) * ℓ * u := by
      have hu := hV.low₂ (-((a⁻¹ : Fˣ) : F)) u u.2
      calc _ = (π (lowerSL (-((a⁻¹ : Fˣ) : F))) * ℓ * (π (lowerSL (-((a⁻¹ : Fˣ) : F))))⁻¹) *
            (π (lowerSL (-((a⁻¹ : Fˣ) : F))) * u * (π (lowerSL (-((a⁻¹ : Fˣ) : F))))⁻¹) := by group
        _ = _ := by
          rw [hV.low_conj, hu, mul_assoc (u : G), mul_inv_cancel, mul_one]
    have e3 : π (upperSL (a : F)) * ((m : G) * ℓ * u) * (π (upperSL (a : F)))⁻¹ =
        ((hV.lam a m : G) * m) * ℓ * ((hV.lam a u : G) * u) := by
      have hℓ' := hV.up₁ (a : F) ℓ ℓ.2
      calc _ = (π (upperSL (a : F)) * m * (π (upperSL (a : F)))⁻¹) *
            (π (upperSL (a : F)) * ℓ * (π (upperSL (a : F)))⁻¹) *
            (π (upperSL (a : F)) * u * (π (upperSL (a : F)))⁻¹) := by group
        _ = _ := by
          rw [hV.up_conj, hV.up_conj, hℓ', mul_assoc (ℓ : G), mul_inv_cancel, mul_one]
    calc π (upperSL (a : F)) * π (lowerSL (-((a⁻¹ : Fˣ) : F))) * π (upperSL (a : F)) * u *
          (π (upperSL (a : F)) * π (lowerSL (-((a⁻¹ : Fˣ) : F))) * π (upperSL (a : F)))⁻¹ =
        π (upperSL (a : F)) * (π (lowerSL (-((a⁻¹ : Fˣ) : F))) *
          (π (upperSL (a : F)) * u * (π (upperSL (a : F)))⁻¹) *
          (π (lowerSL (-((a⁻¹ : Fˣ) : F))))⁻¹) * (π (upperSL (a : F)))⁻¹ := by group
      _ = ((hV.lam a m : G) * m) * ℓ * ((hV.lam a u : G) * u) := by rw [e1, e2, e3]
      _ = _ := by
        have c1 := hV.comm₁₂ _ ℓ.2 _ m.2
        have c2 := hV.comm₁₂ _ (hV.lam a u).2 _ m.2
        calc (hV.lam a m : G) * m * ℓ * ((hV.lam a u : G) * u)
            = (hV.lam a m : G) * (m * ℓ) * (hV.lam a u : G) * u := by group
          _ = (hV.lam a m : G) * (ℓ * m) * (hV.lam a u : G) * u := by rw [c1]
          _ = (hV.lam a m : G) * ℓ * (m * (hV.lam a u : G)) * u := by group
          _ = (hV.lam a m : G) * ℓ * ((hV.lam a u : G) * m) * u := by rw [c2]
          _ = _ := by group
  have hcomm : ∀ c : F, π (upperSL c) * (π (weylSL a) * u * (π (weylSL a))⁻¹) =
      π (weylSL a) * u * (π (weylSL a))⁻¹ * π (upperSL c) := by
    intro c
    set c' : F := -(c * ((a : F) ^ 2)⁻¹) with hc'
    have hc'' : -((a : F) ^ 2 * c') = c := by
      have ha : (a : F) ≠ 0 := a.ne_zero
      rw [hc']
      field_simp
    have hup : π (upperSL c) = π (weylSL a) * π (lowerSL c') * (π (weylSL a))⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, weylSL_mul_lowerSL, mul_inv_cancel_right, hc'']
    have hl := hV.low₂ c' u u.2
    rw [hup]
    calc π (weylSL a) * π (lowerSL c') * (π (weylSL a))⁻¹ * (π (weylSL a) * u * (π (weylSL a))⁻¹)
        = π (weylSL a) * (π (lowerSL c') * u) * (π (weylSL a))⁻¹ := by group
      _ = π (weylSL a) * (u * π (lowerSL c')) * (π (weylSL a))⁻¹ := by rw [hl]
      _ = _ := by group
  have hmu : (m : G) * u = 1 := by
    apply hV.eq_one_of_commute_upper (v₁ := (hV.lam a m : G) * ℓ * hV.lam a u)
    · exact V₁.mul_mem (V₁.mul_mem (hV.lam a m).2 ℓ.2) (hV.lam a u).2
    · exact V₂.mul_mem m.2 u.2
    · intro c
      rw [← hexp]
      exact hcomm c
  have hm' : m = u⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv]
    exact eq_inv_of_mul_eq_one_left hmu
  refine ⟨?_, ?_⟩
  · rw [hexp, hmu, mul_one, hm', map_inv]
    simp only [Subgroup.coe_inv]
    rw [hℓ]
    group
  · have h1 : hV.mu (-((a⁻¹ : Fˣ) : F)) ℓ = u⁻¹ := hm'
    rw [hV.mu_neg] at h1
    exact inv_injective h1

variable [Finite F]

theorem lam_bijective (a : Fˣ) : Function.Bijective (hV.lam a) := by
  have hinj : Function.Injective (hV.lam a) := by
    intro u v huv
    have hu := (hV.weyl_conj a u).2
    have hv := (hV.weyl_conj a v).2
    rw [← hu, ← hv, huv]
  have : Finite V₂ := Nat.finite_of_card_ne_zero (by rw [hV.card₂]; exact Nat.card_pos.ne')
  have : Finite V₁ := Nat.finite_of_card_ne_zero (by rw [hV.card₁]; exact Nat.card_pos.ne')
  exact (Function.Injective.bijective_of_nat_card_le hinj (by rw [hV.card₁, hV.card₂]))

@[expose] noncomputable def lamEquiv (a : Fˣ) : V₂ ≃* V₁ :=
  MulEquiv.ofBijective (hV.lam a) (hV.lam_bijective a)

theorem lamEquiv_apply (a : Fˣ) (u : V₂) : hV.lamEquiv a u = hV.lam a u := rfl

theorem mu_eq_symm (a : Fˣ) (v : V₁) :
    hV.mu ((a⁻¹ : Fˣ) : F) v = (hV.lamEquiv a).symm v := by
  obtain ⟨u, rfl⟩ := (hV.lamEquiv a).surjective v
  rw [MulEquiv.symm_apply_apply, lamEquiv_apply, (hV.weyl_conj a u).2]

@[expose] noncomputable def ell (c : F) : V₁ →* V₁ :=
  (hV.lam c).comp (hV.lamEquiv 1).symm.toMonoidHom

theorem ell_apply (c : F) (v : V₁) : hV.ell c v = hV.lam c ((hV.lamEquiv 1).symm v) := rfl

theorem ell_add (c c' : F) (v : V₁) : hV.ell (c + c') v = hV.ell c v * hV.ell c' v := by
  simp only [ell_apply, lam_add]

theorem ell_zero (v : V₁) : hV.ell 0 v = 1 := hV.lam_zero _

theorem ell_one (v : V₁) : hV.ell 1 v = v := by
  rw [ell_apply]
  have : hV.lam ((1 : Fˣ) : F) ((hV.lamEquiv 1).symm v) = v :=
    (hV.lamEquiv 1).apply_symm_apply v
  simpa using this

theorem diag_conj_one (a : Fˣ) (v : V₁) :
    π (diagSL a) * v * (π (diagSL a))⁻¹ = hV.ell a v := by
  set u := (hV.lamEquiv 1).symm v with hu
  have hv : (v : G) = π (weylSL 1) * u * (π (weylSL 1))⁻¹ := by
    rw [(hV.weyl_conj 1 u).1]
    have : hV.lamEquiv 1 u = v := (hV.lamEquiv 1).apply_symm_apply v
    rw [← lamEquiv_apply, this]
  rw [ell_apply, ← hu, ← (hV.weyl_conj a u).1, diagSL_eq_weylSL, map_mul, map_inv, hv]
  group

theorem ell_mul (c d : F) (v : V₁) : hV.ell c (hV.ell d v) = hV.ell (c * d) v := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_mul, hV.ell_zero, hV.ell_zero]
  by_cases hd : d = 0
  · subst hd
    rw [mul_zero, hV.ell_zero, map_one]
  lift c to Fˣ using IsUnit.mk0 c hc
  lift d to Fˣ using IsUnit.mk0 d hd
  apply Subtype.ext
  have e1 := hV.diag_conj_one d v
  have e2 := hV.diag_conj_one c (hV.ell d v)
  have e3 := hV.diag_conj_one (c * d) v
  rw [Units.val_mul] at e3
  rw [← e2, ← e1, ← e3, ← diagSL_mul, map_mul]
  group

theorem ell_injective (a : Fˣ) : Function.Injective (hV.ell (a : F)) := by
  intro u v huv
  have hu := hV.ell_mul ((a⁻¹ : Fˣ) : F) a u
  have hv := hV.ell_mul ((a⁻¹ : Fˣ) : F) a v
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, hV.ell_one] at hu hv
  rw [← hu, ← hv, huv]

@[expose] noncomputable def xi₁ (e : V₁) (c : F) : V₁ := hV.ell c e

@[expose] noncomputable def xi₂ (e : V₁) (c : F) : V₂ := (hV.lamEquiv 1).symm (hV.xi₁ e c)

theorem xi₁_add (e : V₁) (c c' : F) : hV.xi₁ e (c + c') = hV.xi₁ e c * hV.xi₁ e c' :=
  hV.ell_add c c' e

theorem xi₂_add (e : V₁) (c c' : F) : hV.xi₂ e (c + c') = hV.xi₂ e c * hV.xi₂ e c' := by
  simp only [xi₂, xi₁_add, map_mul]

theorem xi₁_one (e : V₁) : hV.xi₁ e 1 = e := hV.ell_one e

theorem xi₁_mul (e : V₁) (c d : F) : hV.ell c (hV.xi₁ e d) = hV.xi₁ e (c * d) :=
  hV.ell_mul c d e

theorem comm_up (e : V₁) (c d : F) :
    ⁅π (upperSL c), (hV.xi₂ e d : G)⁆ = hV.xi₁ e (c * d) := by
  rw [← hV.lam_coe, xi₂, ← hV.ell_apply, xi₁_mul]

theorem comm_low (e : V₁) (c d : F) :
    ⁅π (lowerSL d), (hV.xi₁ e c : G)⁆ = hV.xi₂ e (d * c) := by
  by_cases hd : d = 0
  · subst hd
    have : hV.xi₂ e 0 = 1 := by
      simp only [xi₂, xi₁, hV.ell_zero, map_one]
    rw [zero_mul, this, lowerSL_zero, map_one]
    simp
  lift d to Fˣ using IsUnit.mk0 d hd
  rw [← hV.mu_coe]
  have h := hV.mu_eq_symm d⁻¹ (hV.xi₁ e c)
  rw [inv_inv] at h
  rw [h]
  congr 1
  rw [MulEquiv.symm_apply_eq, xi₂, lamEquiv_apply]
  have : hV.lam ((d⁻¹ : Fˣ) : F) ((hV.lamEquiv 1).symm (hV.xi₁ e (d * c))) =
      hV.ell ((d⁻¹ : Fˣ) : F) (hV.xi₁ e (d * c)) := rfl
  rw [this, xi₁_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem torus₁ (e : V₁) (a : Fˣ) (c : F) :
    π (diagSL a) * hV.xi₁ e c * (π (diagSL a))⁻¹ = hV.xi₁ e (a * c) := by
  rw [hV.diag_conj_one, xi₁_mul]

theorem xi₂_eq_comm (e : V₁) (c : F) : (hV.xi₂ e c : G) = ⁅π (lowerSL c), (e : G)⁆ := by
  have h := hV.comm_low e 1 c
  rw [mul_one, xi₁_one] at h
  exact h.symm

theorem torus₂ (e : V₁) (a : Fˣ) (c : F) :
    π (diagSL a) * hV.xi₂ e c * (π (diagSL a))⁻¹ = hV.xi₂ e ((a⁻¹ : Fˣ) * c) := by
  rw [hV.xi₂_eq_comm e c]
  have hconj : ∀ x y : G, π (diagSL a) * ⁅x, y⁆ * (π (diagSL a))⁻¹ =
      ⁅π (diagSL a) * x * (π (diagSL a))⁻¹,
        π (diagSL a) * y * (π (diagSL a))⁻¹⁆ := by
    intro x y
    simp only [commutatorElement_def]
    group
  have hlow : π (diagSL a) * π (lowerSL c) * (π (diagSL a))⁻¹ =
      π (lowerSL (((a⁻¹ : Fˣ) : F) ^ 2 * c)) := by
    rw [← map_mul, ← map_inv, ← map_mul, diagSL_mul_lowerSL, mul_inv_cancel_right]
  have he : π (diagSL a) * (e : G) * (π (diagSL a))⁻¹ = hV.xi₁ e a := by
    have := hV.torus₁ e a 1
    rwa [xi₁_one, mul_one] at this
  rw [hconj, hlow, he, comm_low]
  congr 2
  have ha : (a : F) ≠ 0 := a.ne_zero
  simp only [Units.val_inv_eq_inv_val]
  field_simp

theorem weyl₂ (e : V₁) (c : F) :
    π (weylSL 1) * hV.xi₂ e c * (π (weylSL 1))⁻¹ = hV.xi₁ e c := by
  rw [(hV.weyl_conj 1 _).1, ← lamEquiv_apply, xi₂, MulEquiv.apply_symm_apply]

theorem weyl₁ (e : V₁) (c : F) :
    π (weylSL 1) * hV.xi₁ e c * (π (weylSL 1))⁻¹ = hV.xi₂ e (-c) := by
  rw [← hV.weyl₂ e c]
  have h := hV.torus₂ e (-1) c
  have hc : (((-1 : Fˣ)⁻¹ : Fˣ) : F) * c = -c := by simp
  rw [hc, ← weylSL_one_mul_self, map_mul] at h
  rw [← h]
  group

theorem xi₁_injective (e : V₁) (he : e ≠ 1) : Function.Injective (hV.xi₁ e) := by
  intro c c' h
  by_contra hne
  have hsub : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : hV.xi₁ e (c - c') = 1 := by
    have := hV.xi₁_add e (c - c') c'
    rw [sub_add_cancel, h] at this
    exact (mul_eq_right.mp this.symm)
  lift c - c' to Fˣ using IsUnit.mk0 _ hsub with a ha
  apply he
  apply hV.ell_injective a
  rw [map_one]
  exact h1

theorem xi₁_bijective (e : V₁) (he : e ≠ 1) : Function.Bijective (hV.xi₁ e) := by
  have : Finite V₁ := Nat.finite_of_card_ne_zero (by rw [hV.card₁]; exact Nat.card_pos.ne')
  exact (hV.xi₁_injective e he).bijective_of_nat_card_le (by rw [hV.card₁])

theorem xi₂_bijective (e : V₁) (he : e ≠ 1) : Function.Bijective (hV.xi₂ e) :=
  (hV.lamEquiv 1).symm.bijective.comp (hV.xi₁_bijective e he)

end IsRootModuleSL

end Module

end CFSG.GH74.GLS.IVK.Proofs2
