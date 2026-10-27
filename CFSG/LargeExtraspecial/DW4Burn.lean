module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.DW.W4

open Module

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def fixSpace (f : W ≃ₗ[ZMod 2] W) : Submodule (ZMod 2) W :=
  LinearMap.ker ((f : W →ₗ[ZMod 2] W) - LinearMap.id)

theorem mem_fixSpace {f : W ≃ₗ[ZMod 2] W} {w : W} : w ∈ fixSpace f ↔ f w = w := by
  simp [fixSpace, sub_eq_zero]

@[expose] def commSpace (f : W ≃ₗ[ZMod 2] W) : Submodule (ZMod 2) W :=
  LinearMap.range ((f : W →ₗ[ZMod 2] W) - LinearMap.id)

theorem mem_commSpace {f : W ≃ₗ[ZMod 2] W} {w : W} : w ∈ commSpace f ↔ ∃ v, f v - v = w := by
  simp [commSpace]

@[expose] def IsRank2Inv (f : W ≃ₗ[ZMod 2] W) : Prop :=
  f * f = 1 ∧ finrank (ZMod 2) (fixSpace f) = 2

theorem commSpace_le_fixSpace {f : W ≃ₗ[ZMod 2] W} (hf : f * f = 1) :
    commSpace f ≤ fixSpace f := by
  rintro _ ⟨v, rfl⟩
  rw [mem_fixSpace]
  have h2 : f (f v) = v := by
    have := congrArg (fun g : W ≃ₗ[ZMod 2] W => g v) hf
    exact this
  change f (f v - v) = f v - v
  rw [map_sub, h2, ← neg_sub, ZModModule.neg_eq_self]

theorem eq_one_of_fixSpace_eq_top {f : W ≃ₗ[ZMod 2] W} (h : fixSpace f = ⊤) : f = 1 :=
  LinearEquiv.ext fun w => mem_fixSpace.mp (h ▸ Submodule.mem_top : w ∈ fixSpace f)

variable [FiniteDimensional (ZMod 2) W]

theorem finrank_commSpace_add (f : W ≃ₗ[ZMod 2] W) :
    finrank (ZMod 2) (commSpace f) + finrank (ZMod 2) (fixSpace f) = finrank (ZMod 2) W :=
  LinearMap.finrank_range_add_finrank_ker _

theorem two_mul_finrank_fixSpace_ge {f : W ≃ₗ[ZMod 2] W} (hf : f * f = 1) :
    finrank (ZMod 2) W ≤ 2 * finrank (ZMod 2) (fixSpace f) := by
  have h1 := finrank_commSpace_add f
  have h2 := Submodule.finrank_mono (commSpace_le_fixSpace hf)
  omega

theorem card_fixSpace (f : W ≃ₗ[ZMod 2] W) :
    Nat.card (fixSpace f) = 2 ^ finrank (ZMod 2) (fixSpace f) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem IsRank2Inv.fixSpace_eq_commSpace (hW : finrank (ZMod 2) W = 4) {f : W ≃ₗ[ZMod 2] W}
    (hf : IsRank2Inv f) : commSpace f = fixSpace f :=
  Submodule.eq_of_le_of_finrank_eq (commSpace_le_fixSpace hf.1) (by
    have := finrank_commSpace_add f
    rw [hf.2, hW] at this
    rw [hf.2]
    omega)

theorem IsRank2Inv.exists_sub_eq (hW : finrank (ZMod 2) W = 4) {f : W ≃ₗ[ZMod 2] W}
    (hf : IsRank2Inv f) {w : W} (hw : f w = w) : ∃ v, w = f v - v := by
  have : w ∈ commSpace f := (hf.fixSpace_eq_commSpace hW) ▸ mem_fixSpace.mpr hw
  obtain ⟨v, hv⟩ := mem_commSpace.mp this
  exact ⟨v, hv.symm⟩

theorem IsRank2Inv.exists_basis (hW : finrank (ZMod 2) W = 4) {f : W ≃ₗ[ZMod 2] W}
    (hf : IsRank2Inv f) : ∃ b : Basis (Fin 4) (ZMod 2) W,
      f (b 0) = b 0 + b 2 ∧ f (b 1) = b 1 + b 3 ∧ f (b 2) = b 2 ∧ f (b 3) = b 3 := by
  have hc : finrank (ZMod 2) (commSpace f) = 2 := by
    have := finrank_commSpace_add f
    rw [hf.2, hW] at this
    omega
  let r := Module.finBasisOfFinrankEq (ZMod 2) (commSpace f) hc
  have hr : ∀ i, ∃ v, f v - v = (r i : W) := fun i => mem_commSpace.mp (r i).2
  choose v hv using hr
  have hrfix : ∀ i, f (r i : W) = r i := fun i =>
    mem_fixSpace.mp (commSpace_le_fixSpace hf.1 (r i).2)
  have hrli : LinearIndependent (ZMod 2) (fun i => (r i : W)) :=
    r.linearIndependent.map' (commSpace f).subtype (Submodule.ker_subtype _)
  have hr2 : ∀ a c : ZMod 2, a • (r 0 : W) + c • (r 1 : W) = 0 → a = 0 ∧ c = 0 := by
    intro a c h
    have := (Fintype.linearIndependent_iff.mp hrli) ![a, c] (by simpa [Fin.sum_univ_two] using h)
    exact ⟨this 0, this 1⟩
  let b₀ : Fin 4 → W := ![v 0, v 1, r 0, r 1]
  have hli : LinearIndependent (ZMod 2) b₀ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_four] at hg
    change g 0 • v 0 + g 1 • v 1 + g 2 • (r 0 : W) + g 3 • (r 1 : W) = 0 at hg
    have h1 : g 0 • (r 0 : W) + g 1 • (r 1 : W) = 0 := by
      have e : f (g 0 • v 0 + g 1 • v 1 + g 2 • (r 0 : W) + g 3 • (r 1 : W)) -
          (g 0 • v 0 + g 1 • v 1 + g 2 • (r 0 : W) + g 3 • (r 1 : W)) =
          g 0 • (f (v 0) - v 0) + g 1 • (f (v 1) - v 1) := by
        simp only [map_add, map_smul, hrfix]
        module
      rw [hg, map_zero, sub_zero, hv, hv] at e
      exact e.symm
    obtain ⟨h0, h1'⟩ := hr2 _ _ h1
    rw [h0, h1', zero_smul, zero_smul, zero_add, zero_add] at hg
    obtain ⟨h2, h3⟩ := hr2 _ _ hg
    intro i
    fin_cases i
    exacts [h0, h1', h2, h3]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hW])
  have hb : ∀ i, b i = b₀ i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simp only [hb]
    change f (v 0) = v 0 + (r 0 : W)
    rw [← hv 0]
    abel
  · simp only [hb]
    change f (v 1) = v 1 + (r 1 : W)
    rw [← hv 1]
    abel
  · rw [hb]
    exact hrfix 0
  · rw [hb]
    exact hrfix 1

theorem IsRank2Inv.exists_conj_eq (hW : finrank (ZMod 2) W = 4) {f f' : W ≃ₗ[ZMod 2] W}
    (hf : IsRank2Inv f) (hf' : IsRank2Inv f') : ∃ g : W ≃ₗ[ZMod 2] W, g * f * g⁻¹ = f' := by
  obtain ⟨b, h0, h1, h2, h3⟩ := hf.exists_basis hW
  obtain ⟨b', h0', h1', h2', h3'⟩ := hf'.exists_basis hW
  set g := b.equiv b' (Equiv.refl _) with hg
  have hgb : ∀ i, g (b i) = b' i := fun i => by simp [hg]
  have key : g * f = f' * g := by
    refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
    change g (f (b i)) = f' (g (b i))
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [h0, map_add, hgb, hgb, h0']
    · simp only [Fin.mk_one]
      rw [h1, map_add, hgb, hgb, h1']
    · change g (f (b 2)) = f' (g (b 2))
      rw [h2, hgb, h2']
    · change g (f (b 3)) = f' (g (b 3))
      rw [h3, hgb, h3']
  exact ⟨g, by rw [key, mul_inv_cancel_right]⟩

theorem exists_isRank2Inv (hW : finrank (ZMod 2) W = 4) (E : Subgroup (W ≃ₗ[ZMod 2] W))
    (h2 : ∀ f ∈ E, f * f = 1) (h16 : 16 ≤ Nat.card E) : ∃ f ∈ E, IsRank2Inv f := by
  classical
  by_contra hne
  push Not at hne
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W ≃ₗ[ZMod 2] W => (f : W → W))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have : Fintype W := Fintype.ofFinite W
  have : Fintype E := Fintype.ofFinite E
  have hfix : ∀ g : E, Fintype.card (MulAction.fixedBy W g) = if g = 1 then 16 else 8 := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    have e : Nat.card (MulAction.fixedBy W g) = Nat.card (fixSpace (g : W ≃ₗ[ZMod 2] W)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => by
        rw [MulAction.mem_fixedBy, mem_fixSpace]
        rfl)
    rw [e, card_fixSpace]
    split_ifs with hg1
    · subst hg1
      have htop : fixSpace ((1 : E) : W ≃ₗ[ZMod 2] W) = ⊤ :=
        eq_top_iff.mpr fun w _ => mem_fixSpace.mpr rfl
      rw [htop, finrank_top, hW]
      norm_num
    · have hge := two_mul_finrank_fixSpace_ge (h2 g g.2)
      have hle := Submodule.finrank_le (fixSpace (g : W ≃ₗ[ZMod 2] W))
      have hne4 : finrank (ZMod 2) (fixSpace (g : W ≃ₗ[ZMod 2] W)) ≠ 4 := fun h =>
        hg1 (Subtype.ext (eq_one_of_fixSpace_eq_top
          (Submodule.eq_top_of_finrank_eq (h.trans hW.symm))))
      have hne2 : finrank (ZMod 2) (fixSpace (g : W ≃ₗ[ZMod 2] W)) ≠ 2 := fun h =>
        hne g g.2 ⟨h2 g g.2, h⟩
      rw [hW] at hge hle
      have h3 : finrank (ZMod 2) (fixSpace (g : W ≃ₗ[ZMod 2] W)) = 3 := by omega
      rw [h3]
      norm_num
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E W
  simp only [hfix] at hB
  have hsum : ∑ g : E, (if g = 1 then 16 else 8 : ℕ) = 8 * Fintype.card E + 8 := by
    have h : ∀ g : E, (if g = 1 then 16 else 8 : ℕ) = 8 + if g = 1 then 8 else 0 := fun g => by
      split_ifs <;> rfl
    simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hsum] at hB
  have hdvd : Fintype.card E ∣ 8 := by
    have : Fintype.card E ∣ 8 * Fintype.card E + 8 := ⟨_, by rw [hB, mul_comm]⟩
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).mp this
  have := Nat.le_of_dvd (by norm_num) hdvd
  rw [← Nat.card_eq_fintype_card] at this
  omega

theorem eq_zero_of_forall_linearEquiv_bilin (hW : 3 ≤ finrank (ZMod 2) W) (B : W → W → ZMod 2)
    (hadd : ∀ x y y', B x (y + y') = B x y + B x y')
    (hinv : ∀ f : W ≃ₗ[ZMod 2] W, ∀ x y, B (f x) (f y) = B x y) (x w : W) : B x w = 0 := by
  classical
  have hS : Submodule.span (ZMod 2) ((({x, w} : Finset W)) : Set W) ≠ ⊤ := by
    intro h
    have h1 := finrank_span_finset_le_card (R := ZMod 2) ({x, w} : Finset W)
    rw [Set.finrank, h, finrank_top] at h1
    have h2 := Finset.card_le_two (a := x) (b := w)
    omega
  obtain ⟨y, hy⟩ := SetLike.exists_not_mem_of_ne_top _ hS
  obtain ⟨φ, hφy, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hφ : ∀ v ∈ Submodule.span (ZMod 2) ((({x, w} : Finset W)) : Set W), φ v = 0 :=
    fun v hv => by
      have : φ v ∈ (Submodule.span (ZMod 2) ((({x, w} : Finset W)) : Set W)).map φ :=
        Submodule.mem_map_of_mem hv
      rwa [hφS, Submodule.mem_bot] at this
  have hφx : φ x = 0 := hφ x (Submodule.subset_span (by simp))
  have hφw : φ w = 0 := hφ w (Submodule.subset_span (by simp))
  have hφy1 : φ y = 1 := by
    revert hφy
    generalize φ y = a
    revert a
    decide
  have h := hinv (LinearEquiv.transvection hφw) x y
  rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply, hφx, hφy1, zero_smul,
    add_zero, one_smul, hadd] at h
  have h' : B x y + B x w = B x y + 0 := by rw [h, add_zero]
  exact add_left_cancel h'

omit [FiniteDimensional (ZMod 2) W] in
theorem eq_zero_of_forall_linearEquiv_add (hW : 2 ≤ finrank (ZMod 2) W) (Q : W → ZMod 2)
    (hadd : ∀ x y, Q (x + y) = Q x + Q y) (hinv : ∀ f : W ≃ₗ[ZMod 2] W, ∀ x, Q (f x) = Q x)
    (x : W) : Q x = 0 := by
  have h2 : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
  by_cases hx : x = 0
  · subst hx
    exact h2 _ (by rw [← hadd, add_zero])
  · obtain ⟨y, hy⟩ := SetLike.exists_not_mem_of_ne_top ((ZMod 2) ∙ x) (by
      intro h
      have := finrank_span_singleton (K := ZMod 2) hx
      rw [h, finrank_top] at this
      omega)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ Submodule.zero_mem _)
    have hxy0 : x + y ≠ 0 := fun h => hy (by
      rw [show y = -x from (neg_eq_of_add_eq_zero_right h).symm]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self x))
    have heq : ∀ v : W, v ≠ 0 → Q v = Q x := fun v hv => by
      obtain ⟨f, d, hfd, hτ⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_transvection_apply_eq hx hv
      rw [← hτ, hinv]
    refine h2 _ ?_
    calc Q x = Q (x + y) := (heq _ hxy0).symm
      _ = Q x + Q x := by rw [hadd, heq y hy0]

variable {W' : Type*} [AddCommGroup W'] [Module (ZMod 2) W']

omit [FiniteDimensional (ZMod 2) W] in
@[expose] def congrGL (φ : W ≃ₗ[ZMod 2] W') : (W ≃ₗ[ZMod 2] W) ≃* (W' ≃ₗ[ZMod 2] W') where
  toFun f := φ.symm.trans (f.trans φ)
  invFun g := φ.trans (g.trans φ.symm)
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp

omit [FiniteDimensional (ZMod 2) W] in
theorem congrGL_apply (φ : W ≃ₗ[ZMod 2] W') (f : W ≃ₗ[ZMod 2] W) (w : W') :
    congrGL φ f w = φ (f (φ.symm w)) := rfl

omit [FiniteDimensional (ZMod 2) W] in
theorem fixSpace_congrGL (φ : W ≃ₗ[ZMod 2] W') (f : W ≃ₗ[ZMod 2] W) :
    fixSpace (congrGL φ f) = (fixSpace f).map (φ : W →ₗ[ZMod 2] W') := by
  ext w
  rw [mem_fixSpace, congrGL_apply, Submodule.mem_map_equiv, mem_fixSpace]
  constructor
  · intro h
    have := congrArg φ.symm h
    rwa [LinearEquiv.symm_apply_apply] at this
  · intro h
    rw [h, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional (ZMod 2) W] in
theorem isRank2Inv_congrGL_iff (φ : W ≃ₗ[ZMod 2] W')
    (f : W ≃ₗ[ZMod 2] W) : IsRank2Inv (congrGL φ f) ↔ IsRank2Inv f := by
  rw [IsRank2Inv, IsRank2Inv, fixSpace_congrGL, LinearEquiv.finrank_map_eq, ← map_mul,
    (congrGL φ).map_eq_one_iff]

end CFSG.LargeExtraspecial.DW.W4
