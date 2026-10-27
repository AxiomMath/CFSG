module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.AS35QTh

theorem card_linearEquiv (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] :
    Nat.card (W ≃ₗ[ZMod 2] W) = Nat.card (GL (Fin (Module.finrank (ZMod 2) W)) (ZMod 2)) := by
  set b := Module.finBasis (ZMod 2) W
  have e1 : (W ≃ₗ[ZMod 2] W) ≃* (Module.End (ZMod 2) W)ˣ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm
  have e2 : (Module.End (ZMod 2) W)ˣ ≃* GL (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  exact Nat.card_congr (e1.trans e2).toEquiv

theorem not_dvd_card_GL {d : ℕ} (hd : d ≤ 5) :
    ¬ 27 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> simp [Fin.prod_univ_succ]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) V] in
theorem add_self_zmod2 (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 by decide, zero_smul]

@[expose] def stabSub (U : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ u ∈ U, g u = u}
  mul_mem' {g h} hg hh u hu := by
    change g (h u) = u
    rw [hh u hu, hg u hu]
  one_mem' u _ := rfl
  inv_mem' {g} hg u hu := by
    change g.symm u = u
    rw [LinearEquiv.symm_apply_eq, hg u hu]

@[expose] noncomputable def restrictSub (U : Submodule (ZMod 2) V)
    (X : Subgroup (V ≃ₗ[ZMod 2] V)) (hX : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) : X →* (U ≃ₗ[ZMod 2] U) where
  toFun x :=
    { toFun := fun u => ⟨(x : V ≃ₗ[ZMod 2] V) u, hX x x.2 u u.2⟩
      invFun := fun u => ⟨(x : V ≃ₗ[ZMod 2] V).symm u, by
        have := hX x⁻¹ (X.inv_mem x.2) u u.2
        exact this⟩
      map_add' := fun u w => Subtype.ext (map_add _ _ _)
      map_smul' := fun c u => Subtype.ext (map_smul _ _ _)
      left_inv := fun u => Subtype.ext ((x : V ≃ₗ[ZMod 2] V).symm_apply_apply u)
      right_inv := fun u => Subtype.ext ((x : V ≃ₗ[ZMod 2] V).apply_symm_apply u) }
  map_one' := LinearEquiv.ext fun u => Subtype.ext rfl
  map_mul' x y := LinearEquiv.ext fun u => Subtype.ext rfl

variable (X : Subgroup (V ≃ₗ[ZMod 2] V))

theorem zeta_sq_add_of_card (hdim : Module.finrank (ZMod 2) V = 6) (hcard : Nat.card X = 27)
    {ζ : V ≃ₗ[ZMod 2] V} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (hζc : ∀ x ∈ X, ζ * x = x * ζ)
    (hcen : ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c ∈ Subgroup.zpowers ζ) (v : V) :
    ζ (ζ v) + ζ v + v = 0 := by
  classical
  have hζ3v : ∀ w, ζ (ζ (ζ w)) = w := fun w => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f w) hζ3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  set f : V →ₗ[ZMod 2] V := ζ.toLinearMap - LinearMap.id with hf
  have hfw : ∀ w, f w = ζ w - w := fun w => rfl
  set U := LinearMap.range f with hU
  have hgf : ∀ w, ζ (ζ (f w)) + ζ (f w) + f w = 0 := by
    intro w
    rw [hfw, map_sub, map_sub, hζ3v]
    abel
  have hkr : ∀ u ∈ U, ζ u = u → u = 0 := by
    rintro u ⟨w, rfl⟩ hu
    have h := hgf w
    rw [hu, hu, add_self_zmod2, zero_add] at h
    exact h
  have hxU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U := by
    rintro x hx u ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    have hc := congrArg (fun g : V ≃ₗ[ZMod 2] V => g w) (hζc x hx)
    simp only [LinearEquiv.mul_apply] at hc
    rw [hfw, hfw, map_sub, hc]
  have hζU : ζ ∈ stabSub U → False := by
    intro h
    apply hζ1
    refine LinearEquiv.ext fun w => ?_
    have h1 : ζ (f w) = f w := h (f w) ⟨w, rfl⟩
    have h2 := hkr (f w) ⟨w, rfl⟩ h1
    rw [hfw, sub_eq_zero] at h2
    exact h2
  set r := restrictSub U X hxU with hr
  have hinj : Function.Injective r := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hp : IsPGroup 3 X := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
    have : Group.IsNilpotent X := hp.isNilpotent
    have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨⟨c, hcK⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
    obtain ⟨hck, hcc⟩ := hcK
    have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
    have hcU : ∀ u ∈ U, (c : V ≃ₗ[ZMod 2] V) u = u := by
      intro u hu
      have := congrArg (fun g : U ≃ₗ[ZMod 2] U => (g ⟨u, hu⟩ : V)) (MonoidHom.mem_ker.mp hck)
      exact this
    have hcz : (c : V ≃ₗ[ZMod 2] V) ∈ Subgroup.zpowers ζ := by
      refine hcen _ c.2 fun x hx => ?_
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcc ⟨x, hx⟩).symm
    have hc1'' : (c : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hc3 : (c : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ3, one_zpow]
    have hord : ∀ y : V ≃ₗ[ZMod 2] V, y ≠ 1 → y ^ 3 = 1 → orderOf y = 3 := fun y hy hy3 =>
      orderOf_eq_prime hy3 hy
    have hle : Subgroup.zpowers (c : V ≃ₗ[ZMod 2] V) ≤ Subgroup.zpowers ζ :=
      (Subgroup.zpowers_le).mpr hcz
    have : Finite (Subgroup.zpowers ζ) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord _ hζ1 hζ3]; norm_num)
    have heq : Subgroup.zpowers (c : V ≃ₗ[ZMod 2] V) = Subgroup.zpowers ζ :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord _ hζ1 hζ3, hord _ hc1'' hc3])
    have hcS : (c : V ≃ₗ[ZMod 2] V) ∈ stabSub U := hcU
    have hζS : ζ ∈ stabSub U := by
      have : Subgroup.zpowers (c : V ≃ₗ[ZMod 2] V) ≤ stabSub U := (Subgroup.zpowers_le).mpr hcS
      exact this (heq ▸ Subgroup.mem_zpowers ζ)
    exact hζU hζS
  have hdvd : 27 ∣ Nat.card (U ≃ₗ[ZMod 2] U) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_injective r hinj
  rw [card_linearEquiv] at hdvd
  have hle6 : Module.finrank (ZMod 2) U ≤ 6 := hdim ▸ Submodule.finrank_le U
  have hU6 : Module.finrank (ZMod 2) U = 6 := by
    by_contra hne
    exact not_dvd_card_GL (by omega) hdvd
  have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hU6, hdim])
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hUtop
  have hfinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  apply hfinj
  rw [map_zero, map_add, map_add, hfw, hfw, hfw, hζ3v]
  abel

end CFSG.LargeExtraspecial.AS35QTh
