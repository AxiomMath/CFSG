module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

@[expose] def K (g : S →ₗ[ZMod 2] S) : Subalgebra (ZMod 2) (Module.End (ZMod 2) S) :=
  Algebra.adjoin (ZMod 2) {g}

theorem mem_K_iff (g : S →ₗ[ZMod 2] S) (a : Module.End (ZMod 2) S) :
    a ∈ K g ↔ ∃ p : Polynomial (ZMod 2), Polynomial.aeval g p = a := by
  unfold K
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact Iff.rfl

theorem g_mem_K (g : S →ₗ[ZMod 2] S) : g ∈ K g := Algebra.self_mem_adjoin_singleton _ g

theorem K_commute (g : S →ₗ[ZMod 2] S) {a b : Module.End (ZMod 2) S} (ha : a ∈ K g)
    (hb : b ∈ K g) : a * b = b * a := by
  obtain ⟨p, rfl⟩ := (mem_K_iff g a).1 ha
  obtain ⟨q, rfl⟩ := (mem_K_iff g b).1 hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem commute_aeval (g : S →ₗ[ZMod 2] S) {u : Module.End (ZMod 2) S} (hu : u * g = g * u)
    (p : Polynomial (ZMod 2)) : u * Polynomial.aeval g p = Polynomial.aeval g p * u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    have hc : u * (algebraMap (ZMod 2) (Module.End (ZMod 2) S) c) =
        (algebraMap (ZMod 2) (Module.End (ZMod 2) S) c) * u :=
      (Algebra.commutes c u).symm
    have hn : ∀ n : ℕ, u * g ^ n = g ^ n * u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hu, ← mul_assoc]
    rw [← mul_assoc, hc, mul_assoc, hn, mul_assoc]

theorem commute_of_mem_K (g : S →ₗ[ZMod 2] S) {a u : Module.End (ZMod 2) S} (ha : a ∈ K g)
    (hu : u * g = g * u) : u * a = a * u := by
  obtain ⟨p, rfl⟩ := (mem_K_iff g a).1 ha
  exact commute_aeval g hu p

@[expose] def Irr (g : S →ₗ[ZMod 2] S) : Prop :=
  Nontrivial S ∧ ∀ W : Submodule (ZMod 2) S, (∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

theorem injective_of_mem_K {g : S →ₗ[ZMod 2] S} (hg : Irr g) {a : Module.End (ZMod 2) S}
    (ha : a ∈ K g) (h0 : a ≠ 0) : Function.Injective a := by
  have hcomm : a * g = g * a := K_commute g ha (g_mem_K g)
  have hinv : ∀ w ∈ LinearMap.ker a, g w ∈ LinearMap.ker a := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun T => T w) hcomm
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  rcases hg.2 _ hinv with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem card_K {g : S →ₗ[ZMod 2] S} (hg : Irr g) : Nat.card (K g) = Nat.card S := by
  obtain ⟨hnt, hinvW⟩ := hg
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  let ev : K g →ₗ[ZMod 2] S :=
    (LinearMap.applyₗ s₀).comp (K g).val.toLinearMap
  have hev : ∀ a : K g, ev a = (a : Module.End (ZMod 2) S) s₀ := fun a => rfl
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have ha0 : (a : Module.End (ZMod 2) S) ≠ 0 := fun h => hne (Subtype.ext h)
    have := injective_of_mem_K ⟨hnt, hinvW⟩ a.2 ha0
    apply hs₀
    apply this
    rw [map_zero]
    exact (hev a).symm.trans ha
  have hsurj : Function.Surjective ev := by
    have hW : ∀ w ∈ LinearMap.range ev, g w ∈ LinearMap.range ev := by
      rintro _ ⟨a, rfl⟩
      refine ⟨⟨g * (a : Module.End (ZMod 2) S), mul_mem (g_mem_K g) a.2⟩, ?_⟩
      rw [hev, hev]
      rfl
    rcases hinvW _ hW with h | h
    · exfalso
      have h1 : ev 1 ∈ LinearMap.range ev := ⟨1, rfl⟩
      rw [h, Submodule.mem_bot, hev] at h1
      exact hs₀ (by simpa using h1)
    · exact LinearMap.range_eq_top.1 h
  exact Nat.card_congr (Equiv.ofBijective ev ⟨hinj, hsurj⟩)

theorem mem_K_of_commute {g : S →ₗ[ZMod 2] S} (hg : Irr g) {u : Module.End (ZMod 2) S}
    (hu : u * g = g * u) : u ∈ K g := by
  obtain ⟨hnt, hinvW⟩ := hg
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  let ev : K g →ₗ[ZMod 2] S :=
    (LinearMap.applyₗ s₀).comp (K g).val.toLinearMap
  have hev : ∀ a : K g, ev a = (a : Module.End (ZMod 2) S) s₀ := fun a => rfl
  have hsurj : Function.Surjective ev := by
    have hW : ∀ w ∈ LinearMap.range ev, g w ∈ LinearMap.range ev := by
      rintro _ ⟨a, rfl⟩
      refine ⟨⟨g * (a : Module.End (ZMod 2) S), mul_mem (g_mem_K g) a.2⟩, ?_⟩
      rw [hev, hev]
      rfl
    rcases hinvW _ hW with h | h
    · exfalso
      have h1 : ev 1 ∈ LinearMap.range ev := ⟨1, rfl⟩
      rw [h, Submodule.mem_bot, hev] at h1
      exact hs₀ (by simpa using h1)
    · exact LinearMap.range_eq_top.1 h
  obtain ⟨c, hc⟩ := hsurj (u s₀)
  have hcu : (c : Module.End (ZMod 2) S) s₀ = u s₀ := (hev c).symm.trans hc
  have : u = (c : Module.End (ZMod 2) S) := by
    ext v
    obtain ⟨a, rfl⟩ := hsurj v
    have hca : u * (a : Module.End (ZMod 2) S) = (a : Module.End (ZMod 2) S) * u :=
      commute_of_mem_K g a.2 hu
    have h1 : u ((a : Module.End (ZMod 2) S) s₀) = (a : Module.End (ZMod 2) S) (u s₀) := by
      have := congrArg (fun T => T s₀) hca
      simpa using this
    have hcomm : (c : Module.End (ZMod 2) S) * (a : Module.End (ZMod 2) S) =
        (a : Module.End (ZMod 2) S) * (c : Module.End (ZMod 2) S) := K_commute g c.2 a.2
    have h2 := congrArg (fun T => T s₀) hcomm
    simp only [Module.End.mul_apply] at h2
    rw [hev a, h1, ← hcu]
    exact h2.symm
  rw [this]
  exact c.2

theorem exists_inverse_in_K {g : S →ₗ[ZMod 2] S} (hg : Irr g) {a : Module.End (ZMod 2) S}
    (ha : a ∈ K g) (h0 : a ≠ 0) : ∃ b ∈ K g, a * b = 1 := by
  have hinj := injective_of_mem_K hg ha h0
  have hfin : Finite (Module.End (ZMod 2) S) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
  have aux : ∀ n m : ℕ, n < m → a ^ n = a ^ m → ∃ b ∈ K g, a * b = 1 := by
    intro n m hnm h
    have hpowinj : Function.Injective (a ^ n) := by
      have := hinj.iterate n
      intro x y hxy
      apply this
      simpa [Module.End.pow_apply] using hxy
    have h1 : a ^ (m - n) = 1 := by
      ext v
      apply hpowinj
      have h2 : a ^ m = a ^ n * a ^ (m - n) := by rw [← pow_add]; congr 1; omega
      have h3 := congrArg (fun T => T v) (h.trans h2)
      simp only [Module.End.mul_apply] at h3
      simpa using h3.symm
    refine ⟨a ^ (m - n - 1), pow_mem ha _, ?_⟩
    rw [← pow_succ', show m - n - 1 + 1 = m - n by omega, h1]
  obtain ⟨n, m, hnm, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · exact aux n m hlt h
  · exact aux m n hgt h.symm

noncomputable abbrev commRingK (g : S →ₗ[ZMod 2] S) : CommRing (K g) :=
  { (K g).toRing with
    mul_comm := fun a b => Subtype.ext (K_commute g a.2 b.2) }

noncomputable abbrev fieldK {g : S →ₗ[ZMod 2] S} (hg : Irr g) : Field (K g) := by
  letI : CommRing (K g) := commRingK g
  have hnt : Nontrivial S := hg.1
  have : Nontrivial (K g) := by
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    refine ⟨⟨1, 0, fun h => hs ?_⟩⟩
    have := congrArg (fun a : K g => (a : Module.End (ZMod 2) S) s) h
    simpa using this
  refine Field.ofIsUnitOrEqZero fun a => ?_
  by_cases ha : a = 0
  · exact Or.inr ha
  · left
    have ha0 : (a : Module.End (ZMod 2) S) ≠ 0 := fun h => ha (Subtype.ext h)
    obtain ⟨b, hb, hab⟩ := exists_inverse_in_K hg a.2 ha0
    exact isUnit_iff_exists_inv.2 ⟨⟨b, hb⟩, Subtype.ext hab⟩

theorem ringAut_eq_one_of_sq {g : S →ₗ[ZMod 2] S} (hg : Irr g)
    (he : Odd (Module.finrank (ZMod 2) S)) (σ : K g ≃+* K g) (hσ : ∀ a, σ (σ a) = a) (a : K g) :
    σ a = a := by
  letI : Field (K g) := fieldK hg
  have hfinEnd : Finite (Module.End (ZMod 2) S) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
  have hfinK : Finite (K g) := Finite.of_injective (fun a : K g => (a : Module.End (ZMod 2) S))
    Subtype.val_injective
  have hcard : Nat.card (K g) = 2 ^ Module.finrank (ZMod 2) S := by
    rw [card_K hg, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h1 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two (K g)
    hcard).1
  have hσ2 : σ * σ = 1 := RingEquiv.ext fun a => hσ a
  have hd1 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hσ2)
  have hd2 : orderOf σ ∣ Module.finrank (ZMod 2) S := h1 ▸ orderOf_dvd_natCard σ
  have hcop : Nat.Coprime 2 (Module.finrank (ZMod 2) S) := (Nat.coprime_two_left).2 he
  have hord : orderOf σ = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2
  have hσ1 : σ = 1 := orderOf_eq_one_iff.1 hord
  rw [hσ1]
  rfl

theorem exists_ringAut_conj {g : S →ₗ[ZMod 2] S} (τ : S ≃ₗ[ZMod 2] S)
    {g' : Module.End (ZMod 2) S} (hg' : g' ∈ K g)
    (hτ : τ.toLinearMap * g = g' * τ.toLinearMap) :
    ∃ σ : K g ≃ₐ[ZMod 2] K g, ∀ a : K g, ((σ a : K g) : Module.End (ZMod 2) S) * τ.toLinearMap =
        τ.toLinearMap * (a : Module.End (ZMod 2) S) := by
  have hfinEnd : Finite (Module.End (ZMod 2) S) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
  have hfinK : Finite (K g) := Finite.of_injective (fun a : K g => (a : Module.End (ZMod 2) S))
    Subtype.val_injective
  set f₀ := τ.conjAlgEquiv (ZMod 2) with hf₀
  have hf₀g : f₀ g = g' := by
    rw [hf₀, LinearEquiv.conjAlgEquiv_apply]
    ext v
    have := congrArg (fun T => T (τ.symm v)) hτ
    simpa using this
  have hmem : ∀ a ∈ K g, f₀ a ∈ K g := by
    intro a ha
    obtain ⟨p, rfl⟩ := (mem_K_iff g a).1 ha
    rw [← Polynomial.aeval_algHom_apply, hf₀g, ← Polynomial.aeval_subalgebra_coe p (K g) ⟨g', hg'⟩]
    exact Subtype.property _
  let φ : K g →ₐ[ZMod 2] K g :=
    AlgHom.codRestrict ((f₀ : Module.End (ZMod 2) S →ₐ[ZMod 2] Module.End (ZMod 2) S).comp
      (K g).val) (K g) (fun a => hmem a a.2)
  have hinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (f₀.injective this)
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  refine ⟨AlgEquiv.ofBijective φ hbij, fun a => ?_⟩
  show f₀ (a : Module.End (ZMod 2) S) * τ.toLinearMap = τ.toLinearMap * (a : Module.End _ _)
  rw [hf₀, LinearEquiv.conjAlgEquiv_apply]
  ext v
  simp

theorem algEquiv_ext_of_apply_g {g : S →ₗ[ZMod 2] S} (σ₁ σ₂ : K g ≃ₐ[ZMod 2] K g)
    (h : σ₁ ⟨g, g_mem_K g⟩ = σ₂ ⟨g, g_mem_K g⟩) : σ₁ = σ₂ := by
  ext a
  obtain ⟨p, hp⟩ := (mem_K_iff g a).1 a.2
  have ha : a = Polynomial.aeval (⟨g, g_mem_K g⟩ : K g) p := by
    apply Subtype.ext
    rw [Polynomial.aeval_subalgebra_coe]
    exact hp.symm
  rw [ha]
  have h1 : σ₁ (Polynomial.aeval (⟨g, g_mem_K g⟩ : K g) p) =
      Polynomial.aeval (σ₁ ⟨g, g_mem_K g⟩) p :=
    (Polynomial.aeval_algHom_apply σ₁.toAlgHom (⟨g, g_mem_K g⟩ : K g) p).symm
  have h2 : σ₂ (Polynomial.aeval (⟨g, g_mem_K g⟩ : K g) p) =
      Polynomial.aeval (σ₂ ⟨g, g_mem_K g⟩) p :=
    (Polynomial.aeval_algHom_apply σ₂.toAlgHom (⟨g, g_mem_K g⟩ : K g) p).symm
  rw [h1, h2, h]

end CFSG.EvenSporadicStandard.M22Std.P21Field
