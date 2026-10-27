module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.PStability.ProjectiveLine
import CFSG.LocalAnalysis.SignalizerFunctor.LinearPrimeExtension
import CFSG.LocalAnalysis.SignalizerFunctor.LinearScalarExtension
import CFSG.LocalAnalysis.SignalizerFunctor.TwoQuadraticEigenvectorSpan
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
public import Mathlib.GroupTheory.Frattini
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

open SignalizerFunctor.Helpers

def IsQuadratic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : LinearMap.GeneralLinearGroup K V) : Prop :=
  (((a : V →ₗ[K] V) - LinearMap.id) * ((a : V →ₗ[K] V) - LinearMap.id)) = 0

def IsIrreducibleAction {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop :=
  ∀ W : Submodule K V,
    (∀ h : H, ∀ w : W, ((h : LinearMap.GeneralLinearGroup K V).val : V →ₗ[K] V) (w : V) ∈ W) →
    W = ⊥ ∨ W = ⊤

private theorem isQuadratic_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {a : LinearMap.GeneralLinearGroup K V} :
    IsQuadratic a ↔ ((a.toLinearEquiv : V →ₗ[K] V) - 1) ^ 2 = 0 := by
  rw [pow_two]
  rfl

theorem quadratic_linear_p_elements
    (p : ℕ) [Fact p.Prime] (K V : Type*) [Field K] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (a : LinearMap.GeneralLinearGroup K V) (ha : IsQuadratic a) :
    a ^ p = 1 ∧ ∀ g : LinearMap.GeneralLinearGroup K V, IsQuadratic (g⁻¹ * a * g) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  have hquad : ((e a).toLinearMap - 1) ^ 2 = 0 := isQuadratic_iff.mp ha
  refine ⟨e.injective ?_, fun g => ?_⟩
  · rw [map_pow, map_one]
    exact quadratic_linear_automorphism_prime_power p _ hquad
  · have hconj := quadratic_ring_element_conjugate (a : V →ₗ[K] V)
      (by simpa only [IsQuadratic, pow_two, Module.End.one_eq_id] using ha) g
    simpa only [IsQuadratic, pow_two, Module.End.one_eq_id, Units.val_mul] using hconj

private theorem eq_one_of_isQuadratic_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : Module.finrank K V ≤ 1)
    {a : LinearMap.GeneralLinearGroup K V} (ha : IsQuadratic a) : a = 1 := by
  rcases Nat.lt_or_eq_of_le hV with hz | ho
  · have : Subsingleton V :=
      (Module.finrank_eq_zero_iff_of_free K V).mp (Nat.lt_one_iff.mp hz)
    exact Units.ext (LinearMap.ext fun v => Subsingleton.elim _ _)
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
    obtain ⟨c, hc, _⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one ho (a.val - LinearMap.id)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hc0 : c * c = 0 := by
      have hq : (((a.val - LinearMap.id) * (a.val - LinearMap.id) : V →ₗ[K] V) v) = 0 := by
        rw [show _ * _ = (0 : V →ₗ[K] V) from ha, LinearMap.zero_apply]
      rw [hc] at hq
      have : (c * c) • v = 0 := by simpa [Module.End.mul_apply, smul_smul] using hq
      exact (smul_eq_zero.mp this).resolve_right hv
    apply Units.ext
    change a.val = LinearMap.id
    apply sub_eq_zero.mp
    simpa [mul_self_eq_zero.mp hc0] using hc

theorem exists_invariant_line_of_common_eigenvector
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hdim : Module.finrank K V = 2)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (v : V) (hv : v ≠ 0)
    (hfix : ∀ h : H, ∃ c : K, (h.val.val : V →ₗ[K] V) v = c • v) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ h : H, ∀ w : W, (h.val.val : V →ₗ[K] V) (w : V) ∈ W := by
  refine ⟨K ∙ v, fun heq => hv (Submodule.span_singleton_eq_bot.mp heq), fun heq => ?_,
    fun h w => ?_⟩
  · have hbound := finrank_span_le_card (R := K) ({v} : Set V)
    rw [heq, finrank_top, hdim] at hbound
    simp at hbound
  · obtain ⟨c, hc⟩ := hfix h
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp w.property
    exact Submodule.mem_span_singleton.mpr ⟨d * c, by rw [← hd, map_smul, hc, smul_smul]⟩

private theorem map_le_of_mem_closure_pair {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) {a b : LinearMap.GeneralLinearGroup K V}
    (ha : IsQuadratic a) (hb : IsQuadratic b)
    (hWa : ∀ w ∈ W, (a.val : V →ₗ[K] V) w ∈ W) (hWb : ∀ w ∈ W, (b.val : V →ₗ[K] V) w ∈ W)
    {x : LinearMap.GeneralLinearGroup K V}
    (hx : x ∈ Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) :
    W.map (x.val : V →ₗ[K] V) ≤ W := by
  have gen (g : LinearMap.GeneralLinearGroup K V) (hg : IsQuadratic g)
      (hgW : ∀ w ∈ W, (g.val : V →ₗ[K] V) w ∈ W) :
      W.map (g.val : V →ₗ[K] V) ≤ W ∧ W.map ((g⁻¹).val : V →ₗ[K] V) ≤ W := by
    constructor
    · rintro z ⟨w, hw, rfl⟩
      exact hgW w hw
    rintro z ⟨w, hw, rfl⟩
    have hstep : ((g⁻¹).val : V →ₗ[K] V) w = w + w - (g.val : V →ₗ[K] V) w := by
      change (g⁻¹).toLinearEquiv w = _
      rw [LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
      simpa using quadratic_linear_inverse_apply g.toLinearEquiv (isQuadratic_iff.mp hg) w
    rw [hstep]
    exact W.sub_mem (W.add_mem hw hw) (hgW w hw)
  refine (Subgroup.closure_induction
    (p := fun x _ => W.map (x.val : V →ₗ[K] V) ≤ W ∧ W.map ((x⁻¹).val : V →ₗ[K] V) ≤ W)
    ?_ ?_ ?_ ?_ hx).1
  · rintro y (rfl | rfl)
    · exact gen _ ha hWa
    · exact gen _ hb hWb
  · simp [Module.End.one_eq_id]
  · intro y z _ _ hy hz
    constructor
    · rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]
      exact (Submodule.map_mono hz.1).trans hy.1
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]
      exact (Submodule.map_mono hy.2).trans hz.2
  · intro y _ hy
    exact ⟨hy.2, by simpa using hy.1⟩

private theorem finrank_le_two_of_isIrreducibleAction {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    {a b : LinearMap.GeneralLinearGroup K V} (ha : IsQuadratic a) (hb : IsQuadratic b)
    (hirr : IsIrreducibleAction
      (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))) :
    Module.finrank K V ≤ 2 := by
  refine two_quadratic_irreducible_dimension_le_two (FieldType := K) (VectorType := V)
    a.toLinearEquiv b.toLinearEquiv (isQuadratic_iff.mp ha) (isQuadratic_iff.mp hb)
    fun W hWa hWb => hirr W fun h w => ?_
  exact map_le_of_mem_closure_pair W ha hb hWa hWb h.property
    (Submodule.mem_map_of_mem (f := ((h : LinearMap.GeneralLinearGroup K V).val : V →ₗ[K] V))
      w.property)

section Restriction

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (H : Subgroup (LinearMap.GeneralLinearGroup K V)) (W : Submodule K V)
  (hW : ∀ h : H, ∀ w : W, (h.val.val : V →ₗ[K] V) w ∈ W)

private abbrev linearAction : H →* (V ≃ₗ[K] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp H.subtype

private def restriction : H →* LinearMap.GeneralLinearGroup K W :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.toMonoidHom.comp
    (invariantLinearRestriction (linearAction H) W fun h v hv => hW h ⟨v, hv⟩)

private def quotient : H →* LinearMap.GeneralLinearGroup K (V ⧸ W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (V ⧸ W)).symm.toMonoidHom.comp
    (invariantLinearQuotient (linearAction H) W fun h v hv => hW h ⟨v, hv⟩)

private theorem restriction_apply (h : H) (w : W) :
    ((restriction H W hW h).val w : V) = h.val.val w :=
  invariant_linear_restriction_apply (linearAction H) W _ h w

private theorem quotient_apply (h : H) (v : V) :
    (quotient H W hW h).val (Submodule.Quotient.mk v) = Submodule.Quotient.mk (h.val.val v) :=
  invariant_linear_quotient_apply (linearAction H) W _ h v

private theorem restriction_isQuadratic (h : H) (hh : IsQuadratic h.val) :
    IsQuadratic (restriction H W hW h) := by
  unfold IsQuadratic
  refine LinearMap.ext fun w => Subtype.ext ?_
  have he := congrArg (fun f : V →ₗ[K] V => f (w : V)) hh
  simpa [Module.End.mul_apply, LinearMap.sub_apply, restriction_apply, map_sub] using he

private theorem quotient_isQuadratic (h : H) (hh : IsQuadratic h.val) :
    IsQuadratic (quotient H W hW h) := by
  unfold IsQuadratic
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := W.mkQ_surjective x
  have he := congrArg (fun f : V →ₗ[K] V => W.mkQ (f v)) hh
  simpa [Module.End.mul_apply, LinearMap.sub_apply, quotient_apply, map_sub] using he

private theorem isPGroup_of_restriction_of_quotient (p : ℕ) [Fact p.Prime] [CharP K p]
    [FiniteDimensional K V] [Finite H] (hWp : IsPGroup p (restriction H W hW).range)
    (hQp : IsPGroup p (quotient H W hW).range) : IsPGroup p H := by
  have key {U : Type v} [AddCommGroup U] [Module K U] (f : H →* (U ≃ₗ[K] U))
      (hf : IsPGroup p
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.toMonoidHom.comp f).range) :
      IsPGroup p f.range := by
    have hcomp : (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).toMonoidHom.comp
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.toMonoidHom.comp f) = f :=
      MonoidHom.ext fun x => by simp
    have := hf.map (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).toMonoidHom
    rwa [← MonoidHom.range_comp, hcomp] at this
  exact faithful_linear_prime_extension p (linearAction H)
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective.comp Subtype.val_injective)
    W _ (key _ hWp) (key _ hQp)

end Restriction

private theorem range_eq_closure_pair {G A : Type*} [Group G] [Group A] (a b : A)
    (f : Subgroup.closure ({a, b} : Set A) →* G) :
    f.range = Subgroup.closure ({f ⟨a, Subgroup.subset_closure (by simp)⟩,
      f ⟨b, Subgroup.subset_closure (by simp)⟩} : Set G) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl (congrArg f (Subtype.ext hy))
    · exact Or.inr (congrArg f (Subtype.ext hy))
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

private theorem closure_isPElement_range {G A : Type*} [Group G] [Group A]
    (p : ℕ) [Fact p.Prime] {a b : A} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (f : Subgroup.closure ({a, b} : Set A) →* G) :
    Subgroup.closure {h : f.range | IsPElement p h} = ⊤ := by
  let aH : Subgroup.closure ({a, b} : Set A) := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bH : Subgroup.closure ({a, b} : Set A) := ⟨b, Subgroup.subset_closure (by simp)⟩
  have haH : aH ^ p = 1 := Subtype.ext ha
  have hbH : bH ^ p = 1 := Subtype.ext hb
  have ht := f.rangeRestrict.range_eq_top_of_surjective f.rangeRestrict_surjective
  rw [range_eq_closure_pair a b f.rangeRestrict] at ht
  rw [eq_top_iff, ← ht]
  refine Subgroup.closure_mono ?_
  rintro h (rfl | rfl)
  · exact exists_orderOf_eq_prime_pow_iff.mpr ⟨1, by rw [pow_one, ← map_pow, haH, map_one]⟩
  · exact exists_orderOf_eq_prime_pow_iff.mpr ⟨1, by rw [pow_one, ← map_pow, hbH, map_one]⟩

private noncomputable def coordProjection (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hdim : Module.finrank K V = 2) :
    LinearMap.GeneralLinearGroup K V →* PGL2 K :=
  Matrix.ProjGenLinGroup.mk.comp
    (Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq K V hdim)).symm.toMonoidHom

private theorem exists_common_eigenvector_of_fixed (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hdim : Module.finrank K V = 2)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (x : ProjectiveLine K) (hx : ∀ h : H, coordProjection K V hdim h.val • x = x) :
    ∃ v : V, v ≠ 0 ∧ ∀ h : H, ∃ c : K, h.val.val v = c • v := by
  classical
  let B := Module.finBasisOfFinrankEq K V hdim
  induction x using Projectivization.ind with
  | _ w hw =>
    let v := B.equivFun.symm w
    refine ⟨v, B.equivFun.symm.map_ne_zero_iff.mpr hw, fun h => ?_⟩
    have hh := hx h
    change Matrix.ProjGenLinGroup.mk ((Matrix.GeneralLinearGroup.toLin' B).symm h.val) •
      Projectivization.mk K w hw = Projectivization.mk K w hw at hh
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hh
    obtain ⟨c, hc⟩ := hh
    refine ⟨c, B.equivFun.injective ?_⟩
    have hg : ((Matrix.GeneralLinearGroup.toLin' B).symm h.val) • w =
        B.equivFun (h.val.val v) := by
      have hew := congrArg (fun g : LinearMap.GeneralLinearGroup K V => B.equivFun (g.val v))
        ((Matrix.GeneralLinearGroup.toLin' B).apply_symm_apply h.val)
      simp only [Matrix.GeneralLinearGroup.toLin', MulEquiv.trans_apply,
        LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
        LinearMap.GeneralLinearGroup.ofLinearEquiv, LinearEquiv.symm_symm] at hew
      change B.equivFun (B.equivFun.symm
        ((Matrix.GeneralLinearGroup.toLin ((Matrix.GeneralLinearGroup.toLin' B).symm h.val)).val
          (B.equivFun v))) = B.equivFun (h.val.val v) at hew
      rw [LinearEquiv.apply_symm_apply] at hew
      change (Matrix.GeneralLinearGroup.toLin ((Matrix.GeneralLinearGroup.toLin' B).symm h.val)).val
        (B.equivFun (B.equivFun.symm w)) = B.equivFun (h.val.val v) at hew
      rw [LinearEquiv.apply_symm_apply] at hew
      exact hew
    rw [← hg, map_smul]
    change _ = (c : K) • B.equivFun (B.equivFun.symm w)
    rw [LinearEquiv.apply_symm_apply]
    exact hc.symm

section AlgClosed

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

private theorem isPGroup_closure_pair_of_reducible
    (p : ℕ) [Fact p.Prime] [IsAlgClosed K] [CharP K p] [FiniteDimensional K V]
    {a b : LinearMap.GeneralLinearGroup K V} (ha : IsQuadratic a) (hb : IsQuadratic b)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    [Group.IsSolvable (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hrange : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))))
    (W : Submodule K V) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hW : ∀ h : Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)),
      ∀ w : W, (h.val.val : V →ₗ[K] V) w ∈ W)
    (ih : ∀ (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U],
      Module.finrank K U < Module.finrank K V →
      ∀ (c d : LinearMap.GeneralLinearGroup K U), IsQuadratic c → IsQuadratic d →
      ∀ [Finite (Subgroup.closure ({c, d} : Set (LinearMap.GeneralLinearGroup K U)))]
        [Group.IsSolvable (Subgroup.closure ({c, d} : Set (LinearMap.GeneralLinearGroup K U)))],
      (5 ≤ p ∨
        Odd (Nat.card (Subgroup.closure ({c, d} : Set (LinearMap.GeneralLinearGroup K U))))) →
      IsPGroup p (Subgroup.closure ({c, d} : Set (LinearMap.GeneralLinearGroup K U)))) :
    IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
  let H := Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))
  let aH : H := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bH : H := ⟨b, Subgroup.subset_closure (by simp)⟩
  have image_p (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (hdim : Module.finrank K U < Module.finrank K V)
      (f : H →* LinearMap.GeneralLinearGroup K U) (hc : IsQuadratic (f aH))
      (hd : IsQuadratic (f bH)) : IsPGroup p f.range := by
    have heq := range_eq_closure_pair a b f
    have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
    have : Finite (Subgroup.closure ({f aH, f bH} : Set (LinearMap.GeneralLinearGroup K U))) :=
      heq ▸ inferInstance
    have : Group.IsSolvable
        (Subgroup.closure ({f aH, f bH} : Set (LinearMap.GeneralLinearGroup K U))) :=
      heq ▸ inferInstance
    rw [heq]
    refine ih U hdim (f aH) (f bH) hc hd (hrange.imp_right fun ho => ?_)
    rw [← heq]
    exact ho.of_dvd_nat (Subgroup.card_range_dvd f)
  refine isPGroup_of_restriction_of_quotient H W hW p ?_ ?_
  · exact image_p W (Submodule.finrank_lt hW1) _ (restriction_isQuadratic H W hW aH ha)
      (restriction_isQuadratic H W hW bH hb)
  · have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    have hdim : Module.finrank K (V ⧸ W) < Module.finrank K V := by
      have hpos := Module.finrank_pos (R := K) (M := W)
      have heq := W.finrank_quotient_add_finrank
      omega
    exact image_p (V ⧸ W) hdim _ (quotient_isQuadratic H W hW aH ha)
      (quotient_isQuadratic H W hW bH hb)

private theorem isPGroup_closure_pair_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [IsAlgClosed K] [CharP K p] [FiniteDimensional K V]
    {a b : LinearMap.GeneralLinearGroup K V} (ha : IsQuadratic a) (hb : IsQuadratic b)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    [Group.IsSolvable (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hrange : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) :
    IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
  classical
  induction hn : Module.finrank K V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hsmall : Module.finrank K V ≤ 1
    ·
      obtain rfl := eq_one_of_isQuadratic_of_finrank_le_one hsmall ha
      obtain rfl := eq_one_of_isQuadratic_of_finrank_le_one hsmall hb
      refine fun h => ⟨0, Subtype.ext ?_⟩
      simpa [Subgroup.closure_singleton_one] using h.property
    by_cases hirr : IsIrreducibleAction
      (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))
    ·
      have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
      have htwo : Module.finrank K V = 2 := by
        have := finrank_le_two_of_isIrreducibleAction ha hb hirr
        omega
      let H := Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))
      let f : H →* PGL2 K := (coordProjection K V htwo).comp H.subtype
      have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
      have : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
      have hgen := closure_isPElement_range p (quadratic_linear_p_elements p K V a ha).1
        (quadratic_linear_p_elements p K V b hb).1 f
      obtain ⟨x, hx⟩ := solvable_projective_p_generated_fixed_point p hpodd K f.range hgen
        (hrange.imp_right fun ho => ho.of_dvd_nat (Subgroup.card_range_dvd f))
      obtain ⟨v, hv, hfix⟩ := exists_common_eigenvector_of_fixed K V htwo H x
        fun h => hx (f.rangeRestrict h)
      obtain ⟨W, hW0, hW1, hW⟩ := exists_invariant_line_of_common_eigenvector K V htwo H v hv hfix
      exact ((hirr W hW).elim hW0 hW1).elim
    ·
      simp only [IsIrreducibleAction, not_forall, not_or] at hirr
      obtain ⟨W, hW, hW0, hW1⟩ := hirr
      refine isPGroup_closure_pair_of_reducible p ha hb hrange W hW0 hW1 hW ?_
      intro U _ _ _ hdim c d hc hd _ _ halt
      exact ih (Module.finrank K U) (by omega) hc hd halt rfl

end AlgClosed

open scoped TensorProduct in
theorem isPGroup_closure_pair_of_isQuadratic
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (K V : Type*) [Field K] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (a b : LinearMap.GeneralLinearGroup K V) (ha : IsQuadratic a) (hb : IsQuadratic b)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    [Group.IsSolvable (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hrange : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) :
    IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
  classical
  let L := AlgebraicClosure K
  let eV := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  let eL := LinearMap.GeneralLinearGroup.generalLinearEquiv L (L ⊗[K] V)
  let ext := linearScalarExtension (FieldType := K) (VectorType := V) L
  let φ : LinearMap.GeneralLinearGroup K V →* LinearMap.GeneralLinearGroup L (L ⊗[K] V) :=
    eL.symm.toMonoidHom.comp (ext.comp eV.toMonoidHom)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply eV.injective
    apply linear_scalar_extension_injective (FieldType := K) (VectorType := V) L
    exact eL.symm.injective hxy
  let H := Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))
  let φH : H →* LinearMap.GeneralLinearGroup L (L ⊗[K] V) := φ.comp H.subtype
  have hrange_map : φH.range = H.map φ := by
    change (φ.comp H.subtype).range = H.map φ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hgen : φH.range =
      Subgroup.closure ({φ a, φ b} : Set (LinearMap.GeneralLinearGroup L (L ⊗[K] V))) := by
    rw [hrange_map, show H = Subgroup.closure {a, b} from rfl, MonoidHom.map_closure,
      Set.image_pair]
  have hquad (g : LinearMap.GeneralLinearGroup K V) (hg : IsQuadratic g) : IsQuadratic (φ g) :=
    isQuadratic_iff.mpr (linear_scalar_extension_quadratic L (eV g) (isQuadratic_iff.mp hg))
  have : Finite
      (Subgroup.closure ({φ a, φ b} : Set (LinearMap.GeneralLinearGroup L (L ⊗[K] V)))) :=
    hgen ▸ Finite.of_surjective φH.rangeRestrict φH.rangeRestrict_surjective
  have : Group.IsSolvable
      (Subgroup.closure ({φ a, φ b} : Set (LinearMap.GeneralLinearGroup L (L ⊗[K] V)))) :=
    hgen ▸ Group.isSolvable_of_surjective φH.rangeRestrict_surjective
  have hrange' : 5 ≤ p ∨ Odd (Nat.card
      (Subgroup.closure ({φ a, φ b} : Set (LinearMap.GeneralLinearGroup L (L ⊗[K] V))))) := by
    refine hrange.imp_right fun h => ?_
    rwa [← hgen, hrange_map, ← Nat.card_congr (Subgroup.equivMapOfInjective H φ hφinj).toEquiv]
  have hcrit := isPGroup_closure_pair_of_isAlgClosed p hpodd (hquad a ha) (hquad b hb) hrange'
  rw [← hgen] at hcrit
  exact hcrit.of_injective φH.rangeRestrict fun x y h =>
    Subtype.ext (hφinj (by simpa [φH] using congrArg Subtype.val h))

open scoped IsMulCommutative in
theorem quadratic_elementary_quotient
    (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    (N : Subgroup P) [N.Normal] [CFSG.IsElementaryAbelian p (P ⧸ N)]
    (α : MulAut P) (_hαN : ∀ u : P, u ∈ N ↔ α u ∈ N)
    (β : LinearMap.GeneralLinearGroup (ZMod p) (Additive (P ⧸ N)))
    (hβ : ∀ u : P,
       (β.val : Additive (P ⧸ N) →ₗ[ZMod p] Additive (P ⧸ N))
         (QuotientGroup.mk' N u) = QuotientGroup.mk' N (α u))
    (hquad : ∀ u : P, α (u⁻¹ * α u) = u⁻¹ * α u) :
    IsQuadratic β := by
  have hfix (u : P) : α (α u * u⁻¹) = α u * u⁻¹ := by
    have h1 : (α u)⁻¹ * α (α u) = u⁻¹ * α u := by
      rw [← map_inv, ← map_mul, hquad u]
    have key : α (α u) = α u * (u⁻¹ * α u) := by
      rw [← h1]
      group
    rw [map_mul, map_inv, key]
    group
  have hβV (u : P) : (β : Additive (P ⧸ N) →ₗ[ZMod p] Additive (P ⧸ N))
      (Additive.ofMul (QuotientGroup.mk' N u)) = Additive.ofMul (QuotientGroup.mk' N (α u)) :=
    hβ u
  have hstep (u : P) :
      ((β : Additive (P ⧸ N) →ₗ[ZMod p] Additive (P ⧸ N)) - 1)
        (Additive.ofMul (QuotientGroup.mk' N u)) =
      Additive.ofMul (QuotientGroup.mk' N (α u * u⁻¹)) := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hβV u]
    apply Additive.ext
    simp only [toMul_sub, toMul_ofMul, div_eq_mul_inv, ← map_inv, ← map_mul]
  have hid : (1 : Additive (P ⧸ N) →ₗ[ZMod p] Additive (P ⧸ N)) = LinearMap.id := rfl
  unfold IsQuadratic
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N (Additive.toMul v)
  have hv : v = Additive.ofMul (QuotientGroup.mk' N u) := by
    rw [← ofMul_toMul v, hu]
  rw [← hid, hv, Module.End.mul_apply, LinearMap.zero_apply, hstep u, hstep (α u * u⁻¹),
    hfix u, mul_inv_cancel, map_one, ofMul_one]

theorem frattini_elementary_quotient
    (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    (hP : IsPGroup p P) :
    (frattini P).Characteristic ∧ CFSG.IsElementaryAbelian p (P ⧸ frattini P) := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  exact ⟨inferInstance, CFSG.isElementaryAbelian_quotient_frattini⟩

end CFSG
