module

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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def stab (W : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ w, g w ∈ W ↔ w ∈ W}
  one_mem' := fun w => Iff.rfl
  mul_mem' := fun {a b} ha hb w => by
    show a (b w) ∈ W ↔ w ∈ W
    rw [ha, hb]
  inv_mem' := fun {a} ha w => by
    show a.symm w ∈ W ↔ w ∈ W
    rw [← ha (a.symm w)]
    simp

variable (W : Submodule (ZMod 2) V)

theorem map_eq (g : stab W) : W.map (g.1 : V →ₗ[ZMod 2] V) = W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (g.2 y).2 hy
  · intro hx
    refine ⟨g.1.symm x, ?_, by simp⟩
    have := g.2 (g.1.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.1 hx

@[expose] noncomputable def rW (g : stab W) : W ≃ₗ[ZMod 2] W := (g.1).ofSubmodules W W (map_eq W g)

@[expose] noncomputable def rQ (g : stab W) : (V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W) :=
  Submodule.Quotient.equiv W W g.1 (map_eq W g)

@[simp] theorem rW_apply (g : stab W) (w : W) : ((rW W g w : W) : V) = g.1 w := rfl

@[simp] theorem rQ_mk (g : stab W) (v : V) :
    rQ W g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (g.1 v) := rfl

@[expose] noncomputable def ρW : stab W →* (W ≃ₗ[ZMod 2] W) where
  toFun := rW W
  map_one' := by ext w; rfl
  map_mul' := fun a b => by ext w; rfl

@[expose] noncomputable def ρQ : stab W →* ((V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W)) where
  toFun := rQ W
  map_one' := by
    ext v
    induction v using Submodule.Quotient.induction_on
    rfl
  map_mul' := fun a b => by
    ext v
    induction v using Submodule.Quotient.induction_on
    rfl

theorem card_stab_le [Finite V] {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hY : Y ≤ stab W)
    {a b : ℕ}
    (hA : ∀ Z : Subgroup (W ≃ₗ[ZMod 2] W), ¬ 3 ∣ Nat.card Z → Nat.card Z ≤ a)
    (hB : ∀ Z : Subgroup ((V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W)), ¬ 3 ∣ Nat.card Z → Nat.card Z ≤ b)
    (h3 : ¬ 3 ∣ Nat.card Y) :
    ∃ Kr : Subgroup (V ≃ₗ[ZMod 2] V), Kr ≤ Y ∧ (∀ g ∈ Kr, ∀ u, g u - u ∈ W) ∧
      (∀ g ∈ Kr, ∀ w ∈ W, g w = w) ∧ (∀ g ∈ Y, ∀ k ∈ Kr, g * k * g⁻¹ ∈ Kr) ∧
      Nat.card Y ≤ Nat.card Kr * (a * b) := by
  have hfinGL : ∀ (M : Type _) [AddCommGroup M] [Module (ZMod 2) M] [Finite M],
      Finite (M ≃ₗ[ZMod 2] M) := fun M _ _ _ =>
    Finite.of_injective (fun g : M ≃ₗ[ZMod 2] M => (g : M → M)) DFunLike.coe_injective
  have : Finite W := inferInstance
  have : Finite (V ⧸ W) := Quotient.finite _
  have : Finite (W ≃ₗ[ZMod 2] W) := hfinGL W
  have : Finite ((V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W)) := hfinGL (V ⧸ W)
  let ι : Y →* stab W := Subgroup.inclusion hY
  let ρ1 : Y →* (W ≃ₗ[ZMod 2] W) := (ρW W).comp ι
  let ρ2 : Y →* ((V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W)) := (ρQ W).comp ι
  let ρ : Y →* (W ≃ₗ[ZMod 2] W) × ((V ⧸ W) ≃ₗ[ZMod 2] (V ⧸ W)) := ρ1.prod ρ2
  have hker : ρ.ker = ρ1.ker ⊓ ρ2.ker := MonoidHom.ker_prod ρ1 ρ2
  refine ⟨ρ.ker.map Y.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · rintro _ ⟨y, hy, rfl⟩ u
    rw [hker] at hy
    have h2 : ρ2 y = 1 := hy.2
    have h := congrArg (fun φ => φ (Submodule.Quotient.mk u)) h2
    simp only [ρ2, MonoidHom.comp_apply, ρQ, MonoidHom.coe_mk, OneHom.coe_mk] at h
    have h' : (Submodule.Quotient.mk ((y : V ≃ₗ[ZMod 2] V) u) : V ⧸ W) = Submodule.Quotient.mk u := h
    exact (Submodule.Quotient.eq W).1 h'
  · rintro _ ⟨y, hy, rfl⟩ w hw
    rw [hker] at hy
    have h1 : ρ1 y = 1 := hy.1
    have h := congrArg (fun φ => ((φ ⟨w, hw⟩ : W) : V)) h1
    exact h
  · intro g hg k hk
    obtain ⟨k0, hk0, hkk⟩ := Subgroup.mem_map.1 hk
    have hmem : (⟨g, hg⟩ : Y) * k0 * (⟨g, hg⟩ : Y)⁻¹ ∈ ρ.ker :=
      (MonoidHom.normal_ker ρ).conj_mem k0 hk0 ⟨g, hg⟩
    refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
    have : (Y.subtype ((⟨g, hg⟩ : Y) * k0 * (⟨g, hg⟩ : Y)⁻¹)) = g * (Y.subtype k0) * g⁻¹ := by
      simp
    rw [this, hkk]
  · have hinj : Function.Injective Y.subtype := Subtype.coe_injective
    rw [Subgroup.card_map_of_injective hinj]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have hquot : Nat.card (Y ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have hr1 : Nat.card ρ1.range ≤ a := by
      refine hA _ (fun h => h3 ?_)
      exact h.trans (card_range_dvd ρ1)
    have hr2 : Nat.card ρ2.range ≤ b := by
      refine hB _ (fun h => h3 ?_)
      exact h.trans (card_range_dvd ρ2)
    have hle : ρ.range ≤ ρ1.range.prod ρ2.range := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨y, rfl⟩, ⟨y, rfl⟩⟩
    have hrange : Nat.card ρ.range ≤ Nat.card ρ1.range * Nat.card ρ2.range := by
      have h1 := Subgroup.card_le_of_le hle
      rwa [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at h1
    calc Nat.card Y = Nat.card (Y ⧸ ρ.ker) * Nat.card ρ.ker := hmul
      _ = Nat.card ρ.range * Nat.card ρ.ker := by rw [hquot]
      _ ≤ (a * b) * Nat.card ρ.ker := Nat.mul_le_mul_right _ (hrange.trans (Nat.mul_le_mul hr1 hr2))
      _ = Nat.card ρ.ker * (a * b) := by ring

@[expose] noncomputable def kerMap (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ W) (h2 : ∀ g ∈ Kr, ∀ w ∈ W, g w = w) :
    Kr → ((V ⧸ W) →ₗ[ZMod 2] W) := fun g =>
  W.liftQ (((g.1 : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id).codRestrict W (h1 g.1 g.2))
    (fun w hw => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simp [h2 g.1 g.2 w hw])

theorem kerMap_apply (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ W) (h2 : ∀ g ∈ Kr, ∀ w ∈ W, g w = w) (g : Kr) (u : V) :
    ((kerMap W Kr h1 h2 g (Submodule.Quotient.mk u) : W) : V) = g.1 u - u := by
  simp [kerMap]

theorem kerMap_injective (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ W) (h2 : ∀ g ∈ Kr, ∀ w ∈ W, g w = w) :
    Function.Injective (kerMap W Kr h1 h2) := by
  intro g g' h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  have := congrArg (fun φ => ((φ (Submodule.Quotient.mk u) : W) : V)) h
  simp only [kerMap_apply] at this
  exact sub_left_injective this

theorem card_kernel_le [Finite V] (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ W) (h2 : ∀ g ∈ Kr, ∀ w ∈ W, g w = w) :
    Nat.card Kr ≤ 2 ^ (finrank (ZMod 2) W * finrank (ZMod 2) (V ⧸ W)) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Finite ((V ⧸ W) →ₗ[ZMod 2] W) := Module.finite_of_finite (ZMod 2)
  have h3 := Nat.card_le_card_of_injective _ (kerMap_injective W Kr h1 h2)
  have h4 : Nat.card ((V ⧸ W) →ₗ[ZMod 2] W) = 2 ^ (finrank (ZMod 2) W * finrank (ZMod 2) (V ⧸ W)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, Nat.card_zmod, mul_comm]
  omega

theorem kernel_surj [Finite V] (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ W) (h2 : ∀ g ∈ Kr, ∀ w ∈ W, g w = w)
    (hfull : Nat.card Kr = 2 ^ (finrank (ZMod 2) W * finrank (ZMod 2) (V ⧸ W)))
    (l : (V ⧸ W) →ₗ[ZMod 2] W) : ∃ g ∈ Kr, ∀ u, g u - u = (l (Submodule.Quotient.mk u) : V) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Finite ((V ⧸ W) →ₗ[ZMod 2] W) := Module.finite_of_finite (ZMod 2)
  have h4 : Nat.card ((V ⧸ W) →ₗ[ZMod 2] W) = 2 ^ (finrank (ZMod 2) W * finrank (ZMod 2) (V ⧸ W)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, Nat.card_zmod, mul_comm]
  have hbij : Function.Bijective (kerMap W Kr h1 h2) :=
    (kerMap_injective W Kr h1 h2).bijective_of_nat_card_le (by rw [hfull, h4])
  obtain ⟨g, hg⟩ := hbij.2 l
  refine ⟨g.1, g.2, fun u => ?_⟩
  rw [← kerMap_apply W Kr h1 h2 g u, hg]

instance finite_linEquiv {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] :
    Finite (M ≃ₗ[ZMod 2] M) :=
  Finite.of_injective (fun g : M ≃ₗ[ZMod 2] M => (g : M → M)) DFunLike.coe_injective

@[expose] def ThreeBound (n B : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V], finrank (ZMod 2) V = n →
    ∀ Y : Subgroup (V ≃ₗ[ZMod 2] V), ¬ 3 ∣ Nat.card Y → Nat.card Y ≤ B

theorem card_le_of_invariant {n k a b : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (hV : finrank (ZMod 2) V = n) {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    {W : Submodule (ZMod 2) V} (hY : Y ≤ stab W) (hk : finrank (ZMod 2) W = k)
    (hA : ThreeBound k a) (hB : ThreeBound (n - k) b) (h3 : ¬ 3 ∣ Nat.card Y) :
    Nat.card Y ≤ 2 ^ (k * (n - k)) * (a * b) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hq : finrank (ZMod 2) (V ⧸ W) = n - k := by
    have := Submodule.finrank_quotient_add_finrank W
    omega
  have : Finite W := inferInstance
  have : Finite (V ⧸ W) := Quotient.finite _
  obtain ⟨Kr, hKY, h1, h2, -, hcard⟩ := card_stab_le W hY
    (a := a) (b := b) (fun Z hZ => hA W hk Z hZ) (fun Z hZ => hB (V ⧸ W) hq Z hZ) h3
  have hK := card_kernel_le W Kr h1 h2
  rw [hk, hq] at hK
  calc Nat.card Y ≤ Nat.card Kr * (a * b) := hcard
    _ ≤ 2 ^ (k * (n - k)) * (a * b) := Nat.mul_le_mul_right _ hK

@[expose] def conjGL {V V' : Type*} [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid V']
    [Module (ZMod 2) V'] (e : V ≃ₗ[ZMod 2] V') : (V ≃ₗ[ZMod 2] V) ≃* (V' ≃ₗ[ZMod 2] V') where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by ext; simp
  right_inv h := by ext; simp
  map_mul' g h := by ext; simp

theorem add_self_vec {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (u : M) : u + u = 0 := by
  rw [← two_smul (ZMod 2) u]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
