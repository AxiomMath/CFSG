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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2.Sp

open Module

theorem zmod2_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact this a b h

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact this a h

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact this a

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this a

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem vec_add_self (u : W) : u + u = 0 := by
  rw [← two_smul (ZMod 2) u]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem neg_vec (u : W) : -u = u := by
  rw [neg_eq_iff_add_eq_zero, vec_add_self]

theorem vec_eq_of_add_eq_zero {u v : W} (h : u + v = 0) : u = v := by
  rw [eq_neg_of_add_eq_zero_left h, neg_vec]

theorem alt_symm (α : LinearMap.BilinForm (ZMod 2) W) (hα : ∀ u, α u u = 0) (u v : W) :
    α u v = α v u := by
  have h := hα (u + v)
  simp only [map_add, LinearMap.add_apply, hα u, hα v, zero_add, add_zero] at h
  exact (zmod2_add_eq_zero h).symm

structure SpData (ω : LinearMap.BilinForm (ZMod 2) W) (V : Submodule (ZMod 2) W) : Prop where
  alt : ∀ u, ω u u = 0
  nondeg : ω.Nondegenerate
  iso : ∀ v ∈ V, ∀ v' ∈ V, ω v v' = 0
  finrank_W : finrank (ZMod 2) W = 6
  finrank_V : finrank (ZMod 2) V = 3

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

namespace SpData

variable (D : SpData ω V)
include D

theorem symm (u v : W) : ω u v = ω v u := alt_symm ω D.alt u v

theorem perp_eq : ω.orthogonal V = V := by
  refine (Submodule.eq_of_le_of_finrank_le (fun v hv => ?_) ?_).symm
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => D.iso n hn v hv
  · rw [LinearMap.BilinForm.finrank_orthogonal D.nondeg, D.finrank_W, D.finrank_V]

theorem mem_of_forall {x : W} (h : ∀ v ∈ V, ω v x = 0) : x ∈ V := by
  rw [← D.perp_eq]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mpr h

theorem eq_zero_of_forall {x : W} (h : ∀ u, ω x u = 0) : x = 0 :=
  D.nondeg.1 x h

theorem exists_dual (φ : Module.Dual (ZMod 2) W) (hφ : ∀ v ∈ V, φ v = 0) :
    ∃ d ∈ V, ∀ u, ω d u = φ u := by
  refine ⟨(ω.toDual D.nondeg).symm φ, ?_,
    fun u => LinearMap.BilinForm.apply_toDual_symm_apply φ u⟩
  apply D.mem_of_forall
  intro v hv
  rw [D.symm, LinearMap.BilinForm.apply_toDual_symm_apply]
  exact hφ v hv

end SpData

section GL3

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

theorem exists_dual_of_notMem {p : Submodule (ZMod 2) X} {x : X} (hx : x ∉ p) :
    ∃ φ : Module.Dual (ZMod 2) X, φ x = 1 ∧ ∀ y ∈ p, φ y = 0 := by
  obtain ⟨φ, hφx, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨φ, zmod2_eq_one_of_ne_zero hφx, fun y hy => ?_⟩
  have : φ y ∈ p.map φ := ⟨y, hy, rfl⟩
  rw [hφp] at this
  exact this

theorem exists_notMem_span_pair (hX : finrank (ZMod 2) X = 3) (x z : X) :
    ∃ y : X, y ∉ Submodule.span (ZMod 2) {x, z} := by
  by_contra hcon
  push Not at hcon
  classical
  have htop : Submodule.span (ZMod 2) {x, z} = ⊤ := eq_top_iff.mpr fun y _ => hcon y
  have h1 := finrank_span_le_card (R := ZMod 2) ({x, z} : Set X)
  have h2 : (({x, z} : Set X).toFinset).card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  rw [htop, finrank_top, hX] at h1
  omega

theorem exists_ne_zero_mem_ker (hX : finrank (ZMod 2) X = 3) (φ : Module.Dual (ZMod 2) X) :
    ∃ c : X, c ≠ 0 ∧ φ c = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    exact hcon (a - b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab]; exact sub_self _)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [hX, finrank_self] at this
  omega

theorem exists_ne_zero_mem_ker₂ (hX : finrank (ZMod 2) X = 3) (φ ψ : Module.Dual (ZMod 2) X) :
    ∃ c : X, c ≠ 0 ∧ φ c = 0 ∧ ψ c = 0 := by
  let f : X →ₗ[ZMod 2] ZMod 2 × ZMod 2 := LinearMap.prod φ ψ
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank (ZMod 2) (LinearMap.range f) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have h3 : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨c, hc0, ?_, ?_⟩
  · have := congrArg Prod.fst (LinearMap.mem_ker.mp hc)
    exact this
  · have := congrArg Prod.snd (LinearMap.mem_ker.mp hc)
    exact this

theorem exists_apply_ne (hX : finrank (ZMod 2) X = 3) {x : X} (hx : x ≠ 0) :
    ∃ h : X ≃ₗ[ZMod 2] X, h x ≠ x := by
  obtain ⟨φ, hφx, -⟩ := exists_dual_of_notMem (p := ⊥) (x := x) (by simpa using hx)
  obtain ⟨c, hc0, hφc⟩ := exists_ne_zero_mem_ker hX φ
  refine ⟨LinearEquiv.transvection hφc, ?_⟩
  rw [LinearEquiv.transvection.apply, hφx, one_smul]
  intro h
  apply hc0
  simpa using h

theorem exists_fix_apply_eq (hX : finrank (ZMod 2) X = 3) {a x y : X}
    (hx : x ∉ Submodule.span (ZMod 2) {a}) (hy : y ∉ Submodule.span (ZMod 2) {a}) :
    ∃ h : X ≃ₗ[ZMod 2] X, h a = a ∧ h x = y := by
  have hxp : x ∉ Submodule.span (ZMod 2) {a, x + y} := by
    intro hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    rcases zmod2_cases β with rfl | rfl
    · apply hx
      rw [zero_smul, add_zero] at hαβ
      rw [← hαβ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    · apply hy
      rw [one_smul] at hαβ
      have h3 : (α • a + y) + (x + x) = 0 := by
        calc (α • a + y) + (x + x) = (α • a + (x + y)) + x := by abel
          _ = x + x := by rw [hαβ]
          _ = 0 := vec_add_self x
      rw [vec_add_self, add_zero] at h3
      have : y = α • a := (vec_eq_of_add_eq_zero (by rwa [add_comm] at h3))
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  obtain ⟨φ, hφx, hφp⟩ := exists_dual_of_notMem hxp
  have hφa : φ a = 0 := hφp a (Submodule.subset_span (by simp))
  have hφxy : φ (x + y) = 0 := hφp _ (Submodule.subset_span (by simp))
  refine ⟨LinearEquiv.transvection hφxy, ?_, ?_⟩
  · rw [LinearEquiv.transvection.apply, hφa, zero_smul, add_zero]
  · rw [LinearEquiv.transvection.apply, hφx, one_smul, ← add_assoc, vec_add_self, zero_add]

theorem alt_form_eq_zero (hX : finrank (ZMod 2) X = 3) (β : LinearMap.BilinForm (ZMod 2) X)
    (halt : ∀ x, β x x = 0)
    (hinv : ∀ h : X ≃ₗ[ZMod 2] X, ∀ x y, β (h x) (h y) = β x y) (x z : X) : β x z = 0 := by
  by_cases hz : z ∈ Submodule.span (ZMod 2) {x}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, map_zero]
    · rw [one_smul]; exact halt x
  · obtain ⟨y, hy⟩ := exists_notMem_span_pair hX x z
    obtain ⟨φ, hφy, hφp⟩ := exists_dual_of_notMem hy
    have hφx : φ x = 0 := hφp x (Submodule.subset_span (by simp))
    have hφz : φ z = 0 := hφp z (Submodule.subset_span (by simp))
    have h := hinv (LinearEquiv.transvection hφz) x y
    rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply, hφx, hφy, zero_smul,
      add_zero, one_smul, map_add] at h
    exact add_eq_left.mp h

theorem exists_notMem_span_singleton (hX : finrank (ZMod 2) X = 3) (c : X) :
    ∃ u : X, u ∉ Submodule.span (ZMod 2) {c} := by
  obtain ⟨u, hu⟩ := exists_notMem_span_pair hX c c
  rw [Set.pair_eq_singleton] at hu
  exact ⟨u, hu⟩

theorem end_eq_zero_or_id (hX : finrank (ZMod 2) X = 3) (ψ : X →ₗ[ZMod 2] X)
    (hcomm : ∀ (h : X ≃ₗ[ZMod 2] X) (x : X), ψ (h x) = h (ψ x)) :
    (∀ x, ψ x = 0) ∨ (∀ x, ψ x = x) := by
  have step : ∀ c : X, c ≠ 0 → ψ c = 0 ∨ ψ c = c := by
    intro c hc
    obtain ⟨u, hu⟩ := exists_notMem_span_singleton hX c
    obtain ⟨φ, hφu, hφp⟩ := exists_dual_of_notMem hu
    have hφc : φ c = 0 := hφp c (Submodule.mem_span_singleton_self c)
    have h := hcomm (LinearEquiv.transvection hφc) u
    rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply, map_add, map_smul, hφu,
      one_smul] at h
    have h2 : ψ c = φ (ψ u) • c := add_left_cancel h
    rcases zmod2_cases (φ (ψ u)) with h0 | h1
    · left; rw [h2, h0, zero_smul]
    · right; rw [h2, h1, one_smul]
  by_cases hex : ∃ c : X, c ≠ 0 ∧ ψ c = c
  · right
    obtain ⟨c, hc0, hc⟩ := hex
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    rcases step x hx0 with hx | hx
    · exfalso
      by_cases hcx : c = x
      · subst hcx
        rw [hx] at hc
        exact hc0 hc.symm
      · have hne : c + x ≠ 0 := fun h0 => hcx (vec_eq_of_add_eq_zero h0)
        rcases step (c + x) hne with h0 | h0
        · rw [map_add, hc, hx, add_zero] at h0
          exact hc0 h0
        · rw [map_add, hc, hx, add_zero] at h0
          apply hx0
          have : c + x = c + 0 := by rw [← h0, add_zero]
          exact add_left_cancel this
    · exact hx
  · left
    push Not at hex
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    rcases step x hx0 with hx | hx
    · exact hx
    · exact absurd hx (hex x hx0)

theorem eq_zero_of_conj (hX : finrank (ZMod 2) X = 3) (ψ : X →ₗ[ZMod 2] X)
    (h : X ≃ₗ[ZMod 2] X) (c : ZMod 2) (hc : ∀ x, h.symm (ψ (h x)) = ψ x + c • x) : c = 0 := by
  have h1 : h.symm.conj ψ = ψ + c • (1 : X →ₗ[ZMod 2] X) := by
    ext x
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact hc x
  have h2 := LinearMap.trace_conj' ψ h.symm
  rw [h1, map_add, map_smul, LinearMap.trace_one, hX] at h2
  have h3 : c • ((3 : ℕ) : ZMod 2) = 0 := by
    have := h2
    rw [smul_eq_mul] at this
    exact (add_eq_left.mp this)
  have h4 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  rw [h4, smul_eq_mul, mul_one] at h3
  exact h3

theorem exists_apply_eq (hX : finrank (ZMod 2) X = 3) {x y : X} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ h : X ≃ₗ[ZMod 2] X, h x = y := by
  have hx' : x ∉ Submodule.span (ZMod 2) {x + y} := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    rcases zmod2_cases r with rfl | rfl
    · rw [zero_smul] at hr
      exact hx hr.symm
    · rw [one_smul] at hr
      apply hy
      have : x + y = x + 0 := by rw [hr, add_zero]
      exact add_left_cancel this
  obtain ⟨φ, hφx, hφp⟩ := exists_dual_of_notMem hx'
  have hφxy : φ (x + y) = 0 := hφp _ (Submodule.mem_span_singleton_self _)
  refine ⟨LinearEquiv.transvection hφxy, ?_⟩
  rw [LinearEquiv.transvection.apply, hφx, one_smul, ← add_assoc, vec_add_self, zero_add]

end GL3

section Gamma

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

variable (ω V) in
structure IsGamma (Γ : Subgroup (W ≃ₗ[ZMod 2] W)) : Prop where
  isom : ∀ γ ∈ Γ, ∀ u v, ω (γ u) (γ v) = ω u v
  stabV : ∀ γ ∈ Γ, ∀ v ∈ V, γ v ∈ V
  onto : ∀ h : V ≃ₗ[ZMod 2] V, ∃ γ ∈ Γ, ∀ v : V, γ (v : W) = (h v : W)

@[expose] def resV (V : Submodule (ZMod 2) W) (γ : W ≃ₗ[ZMod 2] W) (h₁ : ∀ v ∈ V, γ v ∈ V)
    (h₂ : ∀ v ∈ V, γ.symm v ∈ V) : V ≃ₗ[ZMod 2] V where
  toFun v := ⟨γ v, h₁ v v.2⟩
  invFun v := ⟨γ.symm v, h₂ v v.2⟩
  map_add' u w := Subtype.ext (map_add γ _ _)
  map_smul' c u := Subtype.ext (map_smul γ _ _)
  left_inv u := Subtype.ext (γ.symm_apply_apply _)
  right_inv u := Subtype.ext (γ.apply_symm_apply _)

@[simp] theorem coe_resV (γ : W ≃ₗ[ZMod 2] W) (h₁ : ∀ v ∈ V, γ v ∈ V)
    (h₂ : ∀ v ∈ V, γ.symm v ∈ V) (v : V) : ((resV V γ h₁ h₂ v : V) : W) = γ v := rfl

@[simp] theorem coe_resV_symm (γ : W ≃ₗ[ZMod 2] W) (h₁ : ∀ v ∈ V, γ v ∈ V)
    (h₂ : ∀ v ∈ V, γ.symm v ∈ V) (v : V) :
    (((resV V γ h₁ h₂).symm v : V) : W) = γ.symm v := rfl

namespace IsGamma

variable {Γ : Subgroup (W ≃ₗ[ZMod 2] W)} (hΓ : IsGamma ω V Γ)
include hΓ

theorem symm_mem {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) : γ.symm ∈ Γ := Γ.inv_mem hγ

theorem stabV_symm {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) {v : W} (hv : v ∈ V) : γ.symm v ∈ V :=
  hΓ.stabV _ (hΓ.symm_mem hγ) v hv

theorem isom_symm {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) (u v : W) :
    ω (γ.symm u) v = ω u (γ v) := by
  have := hΓ.isom γ hγ (γ.symm u) v
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] def res {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) : V ≃ₗ[ZMod 2] V :=
  resV V γ (hΓ.stabV γ hγ) (fun v hv => hΓ.stabV_symm hγ hv)

@[simp] theorem coe_res {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) (v : V) :
    ((hΓ.res hγ v : V) : W) = γ v := rfl

@[simp] theorem coe_res_symm {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) (v : V) :
    (((hΓ.res hγ).symm v : V) : W) = γ.symm v := rfl

theorem exists_transvection {φ : Module.Dual (ZMod 2) V} {c : V} (h : φ c = 0) :
    ∃ γ ∈ Γ, ∀ v : V, γ (v : W) = (v : W) + φ v • (c : W) := by
  obtain ⟨γ, hγ, hγv⟩ := hΓ.onto (LinearEquiv.transvection h)
  refine ⟨γ, hγ, fun v => ?_⟩
  rw [hγv v, LinearEquiv.transvection.apply]
  rfl

theorem flat_transvection {φ : Module.Dual (ZMod 2) V} {c : V} (h : φ c = 0)
    {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ∈ Γ) (hγφ : ∀ v : V, γ (v : W) = (v : W) + φ v • (c : W))
    (w : W) (v : V) : ω (γ w - w) (v : W) = φ v * ω w (c : W) := by
  set v' : V := ⟨γ.symm (v : W), hΓ.stabV_symm hγ v.2⟩ with hv'
  have e1 : γ (v' : W) = v := by simp [hv']
  have e2 : (v : W) = (v' : W) + φ v' • (c : W) := by rw [← hγφ v']; exact e1.symm
  have e2' : v = v' + φ v' • c := Subtype.ext (by rw [e2]; rfl)
  have e3 : φ v = φ v' := by
    conv_lhs => rw [e2']
    rw [map_add, map_smul, h, smul_eq_mul, mul_zero, add_zero]
  have e4 : (v' : W) = (v : W) + φ v • (c : W) := by
    have : (v' : W) + (v : W) = φ v • (c : W) := by
      rw [e2, ← e3]
      calc (v' : W) + ((v' : W) + φ v • (c : W)) = ((v' : W) + (v' : W)) + φ v • (c : W) := by
            rw [add_assoc]
        _ = φ v • (c : W) := by rw [vec_add_self, zero_add]
    calc (v' : W) = (v : W) + ((v : W) + (v' : W)) := by
          rw [← add_assoc, vec_add_self, zero_add]
      _ = (v : W) + φ v • (c : W) := by rw [add_comm (v : W) (v' : W), this]
  have e5 : ω (γ w) (v : W) = ω w (v' : W) := by
    have := hΓ.isom γ hγ w (v' : W)
    rw [e1] at this
    exact this
  rw [map_sub, LinearMap.sub_apply, e5, e4, map_add, map_smul, smul_eq_mul]
  simp only [add_sub_cancel_left]

theorem invariant_form (D : SpData ω V) (α : LinearMap.BilinForm (ZMod 2) W)
    (hα : ∀ u, α u u = 0)
    (hinv : ∀ γ ∈ Γ, ∃ c : ZMod 2, ∀ u v, α (γ u) (γ v) = α u v + c * ω u v) :
    ∃ c : ZMod 2, ∀ u v, α u v = c * ω u v := by
  have hsymm := alt_symm α hα
  have hVV : ∀ v ∈ V, ∀ v' ∈ V, α v v' = 0 := by
    intro v hv v' hv'
    refine alt_form_eq_zero D.finrank_V (α.compl₁₂ V.subtype V.subtype) (fun x => hα x)
      (fun h x y => ?_) ⟨v, hv⟩ ⟨v', hv'⟩
    obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
    obtain ⟨c, hc⟩ := hinv γ hγ
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply]
    rw [← hγh x, ← hγh y, hc, D.iso x x.2 y y.2, mul_zero, add_zero]
  let ψW : V →ₗ[ZMod 2] W := (ω.toDual D.nondeg).symm.toLinearMap ∘ₗ LinearMap.comp α V.subtype
  have hψW : ∀ (v : V) (u : W), ω (ψW v) u = α v u := fun v u =>
    LinearMap.BilinForm.apply_toDual_symm_apply (B := ω) (hB := D.nondeg) (α (v : W)) u
  have hψV : ∀ v : V, ψW v ∈ V := fun v => D.mem_of_forall fun v' hv' => by
    rw [D.symm, hψW]
    exact hVV v v.2 v' hv'
  let ψ : V →ₗ[ZMod 2] V := ψW.codRestrict V hψV
  have hψ : ∀ (v : V) (u : W), ω (ψ v : W) u = α v u := hψW
  have hrel : ∀ γ (hγ : γ ∈ Γ) (c : ZMod 2), (∀ u v, α (γ u) (γ v) = α u v + c * ω u v) →
      ∀ x : V, (hΓ.res hγ).symm (ψ (hΓ.res hγ x)) = ψ x + c • x := by
    intro γ hγ c hc x
    apply Subtype.ext
    have hsub : ∀ u : W, ω (γ.symm (ψ (hΓ.res hγ x) : W) - ((ψ x : W) + c • (x : W))) u = 0 := by
      intro u
      have e1 : ω (γ.symm (ψ (hΓ.res hγ x) : W)) u = ω (ψ (hΓ.res hγ x) : W) (γ u) :=
        hΓ.isom_symm hγ _ _
      have e2 : ω (ψ (hΓ.res hγ x) : W) (γ u) = α (γ (x : W)) (γ u) := hψ (hΓ.res hγ x) (γ u)
      rw [map_sub, LinearMap.sub_apply, e1, e2, hc, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hψ x u]
      exact sub_self _
    have := D.eq_zero_of_forall hsub
    rw [sub_eq_zero] at this
    exact this
  have hconj : ∀ γ (hγ : γ ∈ Γ) (c : ZMod 2), (∀ u v, α (γ u) (γ v) = α u v + c * ω u v) →
      c = 0 := fun γ hγ c hc =>
    eq_zero_of_conj D.finrank_V ψ (hΓ.res hγ) c (hrel γ hγ c hc)
  have hcomm : ∀ (h : V ≃ₗ[ZMod 2] V) (x : V), ψ (h x) = h (ψ x) := by
    intro h x
    obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
    obtain ⟨c, hc⟩ := hinv γ hγ
    have hc0 := hconj γ hγ c hc
    have hres : hΓ.res hγ = h := LinearEquiv.ext fun v => Subtype.ext (hγh v)
    have := hrel γ hγ c hc x
    rw [hres, hc0, zero_smul, add_zero] at this
    calc ψ (h x) = h (h.symm (ψ (h x))) := (h.apply_symm_apply _).symm
      _ = h (ψ x) := by rw [this]
  obtain ⟨lam, hlam⟩ : ∃ lam : ZMod 2, ∀ v ∈ V, ∀ w, α v w = lam * ω v w := by
    rcases end_eq_zero_or_id D.finrank_V ψ hcomm with h0 | h1
    · refine ⟨0, fun v hv w => ?_⟩
      rw [← hψ ⟨v, hv⟩ w, h0 ⟨v, hv⟩]
      simp
    · refine ⟨1, fun v hv w => ?_⟩
      rw [← hψ ⟨v, hv⟩ w, h1 ⟨v, hv⟩, one_mul]
  refine ⟨lam, fun u u₁ => ?_⟩
  obtain ⟨c, hc0, hcu, hcu₁⟩ := exists_ne_zero_mem_ker₂ D.finrank_V
    (LinearMap.comp (ω u) V.subtype) (LinearMap.comp (ω u₁) V.subtype)
  have hcu' : ω u (c : W) = 0 := hcu
  have hcu₁' : ω u₁ (c : W) = 0 := hcu₁
  obtain ⟨u', hu'⟩ : ∃ u' : W, ω u' (c : W) = 1 := by
    by_contra hcon
    push Not at hcon
    apply hc0
    have : (c : W) = 0 := D.nondeg.2 (c : W) fun x => by
      rcases zmod2_cases (ω x (c : W)) with h | h
      · exact h
      · exact absurd h (hcon x)
    exact Subtype.ext this
  set φ : Module.Dual (ZMod 2) V := LinearMap.comp (ω u₁) V.subtype with hφ
  have hφc : φ c = 0 := hcu₁
  obtain ⟨γ, hγ, hγφ⟩ := hΓ.exists_transvection hφc
  have hflat := fun w v => hΓ.flat_transvection hφc hγ hγφ w v
  have hx1 : γ u - u ∈ V := D.mem_of_forall fun v' hv' => by
    rw [D.symm, hflat u ⟨v', hv'⟩, hcu', mul_zero]
  have hx2 : γ u' - u' - u₁ ∈ V := D.mem_of_forall fun v' hv' => by
    rw [D.symm, map_sub, LinearMap.sub_apply, hflat u' ⟨v', hv'⟩, hu', mul_one]
    exact sub_self _
  obtain ⟨c₀, hc₀⟩ := hinv γ hγ
  have hc₀0 := hconj γ hγ c₀ hc₀
  subst hc₀0
  simp only [zero_mul, add_zero] at hc₀
  have E1 := hc₀ u u'
  have E2 := hΓ.isom γ hγ u u'
  set x1 := γ u - u with hx1def
  set x2 := γ u' - u' - u₁ with hx2def
  have hγu : γ u = u + x1 := by rw [hx1def]; abel
  have hγu' : γ u' = u' + u₁ + x2 := by rw [hx2def]; abel
  rw [hγu, hγu'] at E1 E2
  have h1 : α x1 u' = lam * ω x1 u' := hlam x1 hx1 u'
  have h2 : α x1 u₁ = lam * ω x1 u₁ := hlam x1 hx1 u₁
  have h3 : α x1 x2 = lam * ω x1 x2 := hlam x1 hx1 x2
  have h4 : α u x2 = lam * ω u x2 := by rw [hsymm u x2, hlam x2 hx2 u, D.symm x2 u]
  simp only [map_add, LinearMap.add_apply] at E1 E2
  rw [h1, h2, h3, h4] at E1
  linear_combination E1 - lam * E2

end IsGamma

end Gamma

section FGroup

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

variable (ω V) in
structure IsF (x : W ≃ₗ[ZMod 2] W) : Prop where
  isom : ∀ u v, ω (x u) (x v) = ω u v
  triv : ∀ v ∈ V, x v = v

namespace IsF

theorem one : IsF ω V (1 : W ≃ₗ[ZMod 2] W) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem mul {x y : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) (hy : IsF ω V y) : IsF ω V (x * y) :=
  ⟨fun u v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx.isom, hy.isom], fun v hv => by
    rw [LinearEquiv.mul_apply, hy.triv v hv, hx.triv v hv]⟩

theorem inv {x : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) : IsF ω V x⁻¹ :=
  ⟨fun u v => by
    have := hx.isom (x⁻¹ u) (x⁻¹ v)
    simpa using this.symm, fun v hv => by
    have := hx.triv v hv
    calc x⁻¹ v = x⁻¹ (x v) := by rw [this]
      _ = v := by simp⟩

theorem conj {x g : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) (hg : ∀ u v, ω (g u) (g v) = ω u v)
    (hgV : ∀ v ∈ V, g v ∈ V) (hgV' : ∀ v ∈ V, g.symm v ∈ V) : IsF ω V (g * x * g⁻¹) :=
  ⟨fun u v => by
    have := hg (x (g.symm u)) (x (g.symm v))
    simp only [LinearEquiv.mul_apply]
    show ω (g (x (g.symm u))) (g (x (g.symm v))) = ω u v
    rw [hg, hx.isom]
    have := hg (g.symm u) (g.symm v)
    simpa using this.symm, fun v hv => by
    simp only [LinearEquiv.mul_apply]
    show g (x (g.symm v)) = v
    rw [hx.triv _ (hgV' v hv)]
    simp⟩

variable (D : SpData ω V) {x : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x)
include D hx

theorem sub_mem (u : W) : x u - u ∈ V := by
  apply D.mem_of_forall
  intro v hv
  rw [D.symm, map_sub, LinearMap.sub_apply]
  have := hx.isom u v
  rw [hx.triv v hv] at this
  rw [this]
  exact sub_self _

theorem rel (u u' : W) : ω (x u - u) u' = ω (x u' - u') u := by
  have ha := hx.sub_mem D u
  have hb := hx.sub_mem D u'
  have h := hx.isom u u'
  have e1 : x u = u + (x u - u) := by abel
  have e2 : x u' = u' + (x u' - u') := by abel
  generalize x u - u = a at ha e1 ⊢
  generalize x u' - u' = b at hb e2 ⊢
  rw [e1, e2] at h
  simp only [map_add, LinearMap.add_apply, D.iso a ha b hb, add_zero] at h
  have h' : ω u b + ω a u' = 0 := by
    have := h
    linear_combination this
  rw [D.symm b u]
  exact (zmod2_add_eq_zero h').symm

theorem theta_add (u u' : W) :
    ω (x (u + u') - (u + u')) (u + u') = ω (x u - u) u + ω (x u' - u') u' := by
  have e : x (u + u') - (u + u') = (x u - u) + (x u' - u') := by rw [map_add]; abel
  rw [e]
  simp only [map_add, LinearMap.add_apply]
  rw [hx.rel D u u']
  have hself := zmod2_add_self (ω (x u' - u') u)
  linear_combination hself

theorem theta_smul (c : ZMod 2) (u : W) :
    ω (x (c • u) - c • u) (c • u) = c • ω (x u - u) u := by
  rcases zmod2_cases c with rfl | rfl
  · simp
  · simp

@[expose] def theta : Module.Dual (ZMod 2) W where
  toFun u := ω (x u - u) u
  map_add' := hx.theta_add D
  map_smul' c u := hx.theta_smul D c u

theorem mul_sub {y : W ≃ₗ[ZMod 2] W} (hy : IsF ω V y) (u : W) :
    (x * y) u - u = (x u - u) + (y u - u) := by
  have hb := hy.sub_mem D u
  have h1 : y u = u + (y u - u) := by abel
  have h2 : x (y u) = x u + (y u - u) := by
    conv_lhs => rw [h1]
    rw [map_add, hx.triv _ hb]
  rw [LinearEquiv.mul_apply, h2]
  abel

theorem theta_mul {y : W ≃ₗ[ZMod 2] W} (hy : IsF ω V y) (u : W) :
    ω ((x * y) u - u) u = ω (x u - u) u + ω (y u - u) u := by
  rw [hx.mul_sub D hy u, map_add, LinearMap.add_apply]

theorem theta_inv (u : W) : ω (x⁻¹ u - u) u = ω (x u - u) u := by
  have h := hx.theta_mul D (hx.inv) u
  rw [mul_inv_cancel, LinearEquiv.coe_one, id_eq, sub_self, map_zero, LinearMap.zero_apply] at h
  exact (zmod2_add_eq_zero h.symm).symm

theorem theta_conj {g : W ≃ₗ[ZMod 2] W} (hg : ∀ u v, ω (g u) (g v) = ω u v) (u : W) :
    ω ((g * x * g⁻¹) u - u) u = ω (x (g.symm u) - g.symm u) (g.symm u) := by
  have e : (g * x * g⁻¹) u = g (x (g.symm u)) := rfl
  have hu : g (g.symm u) = u := g.apply_symm_apply u
  calc ω ((g * x * g⁻¹) u - u) u = ω (g (x (g.symm u)) - g (g.symm u)) (g (g.symm u)) := by
        rw [e, hu]
    _ = ω (g (x (g.symm u) - g.symm u)) (g (g.symm u)) := by rw [map_sub g]
    _ = ω (x (g.symm u) - g.symm u) (g.symm u) := hg _ _

theorem theta_apply (u : W) : hx.theta D u = ω (x u - u) u := rfl

theorem theta_eq_zero_of_mem {v : W} (hv : v ∈ V) : hx.theta D v = 0 := by
  rw [theta_apply]
  have : x v - v = 0 := by rw [hx.triv v hv, sub_self]
  rw [this, map_zero, LinearMap.zero_apply]

end IsF

end FGroup

section Normalizer

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}
  {Γ : Subgroup (W ≃ₗ[ZMod 2] W)}

theorem symm_mem_of_mem {y : W ≃ₗ[ZMod 2] W} (hyV : ∀ v ∈ V, y v ∈ V) {v : W} (hv : v ∈ V) :
    y.symm v ∈ V := by
  have hle : V.map (y : W →ₗ[ZMod 2] W) ≤ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact hyV w hw
  have heq : V.map (y : W →ₗ[ZMod 2] W) = V :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [LinearEquiv.finrank_map_eq])
  rw [← heq] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  simpa using hw

theorem IsGamma.mem_of_normalizes (D : SpData ω V) (hΓ : IsGamma ω V Γ)
    (hΓ0 : ∀ γ ∈ Γ, IsF ω V γ → ∀ u, ω (γ u - u) u = 0)
    (hAlt : ∀ x : W ≃ₗ[ZMod 2] W, IsF ω V x → (∀ u, ω (x u - u) u = 0) → x ∈ Γ)
    {y : W ≃ₗ[ZMod 2] W} (hy : ∀ u v, ω (y u) (y v) = ω u v) (hyV : ∀ v ∈ V, y v ∈ V)
    (hyN : ∀ γ ∈ Γ, y * γ * y⁻¹ ∈ Γ) : y ∈ Γ := by
  have hyV' : ∀ v ∈ V, y.symm v ∈ V := fun v hv => symm_mem_of_mem hyV hv
  obtain ⟨γ, hγ, hγy⟩ := hΓ.onto (resV V y hyV (fun v hv => hyV' v hv))
  have hγy' : ∀ v ∈ V, γ v = y v := fun v hv => hγy ⟨v, hv⟩
  have hγi : γ⁻¹ ∈ Γ := Γ.inv_mem hγ
  set y' : W ≃ₗ[ZMod 2] W := γ⁻¹ * y with hy'
  have hy'F : IsF ω V y' := ⟨fun u v => by
      show ω (γ.symm (y u)) (γ.symm (y v)) = ω u v
      rw [← hy u v]
      have := hΓ.isom γ⁻¹ hγi (y u) (y v)
      exact this, fun v hv => by
      show γ.symm (y v) = v
      rw [← hγy' v hv]
      simp⟩
  have hy'N : ∀ g ∈ Γ, y' * g * y'⁻¹ ∈ Γ := by
    intro g hg
    have : y' * g * y'⁻¹ = γ⁻¹ * (y * g * y⁻¹) * γ := by rw [hy']; group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem hγi (hyN g hg)) hγ
  have hinv : ∀ g ∈ Γ, ∀ u, ω (y' (g.symm u) - g.symm u) (g.symm u) = ω (y' u - u) u := by
    intro g hg u
    have hgF : ∀ u v, ω (g u) (g v) = ω u v := hΓ.isom g hg
    have hconjF : IsF ω V (g * y'⁻¹ * g⁻¹) :=
      (hy'F.inv).conj hgF (hΓ.stabV g hg) (fun v hv => hΓ.stabV_symm hg hv)
    have hzF : IsF ω V (y' * (g * y'⁻¹ * g⁻¹)) := hy'F.mul hconjF
    have hz : y' * (g * y'⁻¹ * g⁻¹) ∈ Γ := by
      have : y' * (g * y'⁻¹ * g⁻¹) = (y' * g * y'⁻¹) * g⁻¹ := by group
      rw [this]
      exact Γ.mul_mem (hy'N g hg) (Γ.inv_mem hg)
    have h0 := hΓ0 _ hz hzF u
    rw [hy'F.theta_mul D hconjF u, (hy'F.inv).theta_conj D hgF u,
      hy'F.theta_inv D (g.symm u)] at h0
    exact (zmod2_add_eq_zero h0).symm
  have hθV : ∀ v ∈ V, hy'F.theta D v = 0 := fun v hv => hy'F.theta_eq_zero_of_mem D hv
  obtain ⟨d, hdV, hd⟩ := D.exists_dual (hy'F.theta D) hθV
  have hdfix : ∀ g ∈ Γ, g d = d := by
    intro g hg
    have key : ∀ u, ω (g d) u = ω d u := by
      intro u
      have h1 := hΓ.isom g hg d (g.symm u)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [h1, hd (g.symm u), hd u]
      exact hinv g hg u
    apply sub_eq_zero.mp
    apply D.eq_zero_of_forall
    intro u
    rw [map_sub, LinearMap.sub_apply, key u, sub_self]
  have hd0 : d = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := exists_apply_ne D.finrank_V (x := (⟨d, hdV⟩ : V))
      (fun h => hne (congrArg Subtype.val h))
    obtain ⟨γ', hγ', hγ'h⟩ := hΓ.onto h
    apply hh
    apply Subtype.ext
    rw [← hγ'h ⟨d, hdV⟩]
    exact hdfix γ' hγ'
  have hy'Γ : y' ∈ Γ := by
    apply hAlt y' hy'F
    intro u
    have := hd u
    rw [hd0, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have : y = γ * y' := by rw [hy']; group
  rw [this]
  exact Γ.mul_mem hγ hy'Γ

end Normalizer

section Alt

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

variable (ω V) in
@[expose] def AltGrp (D : SpData ω V) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {x | IsF ω V x ∧ ∀ u, ω (x u - u) u = 0}
  mul_mem' := fun {x y} hx hy => ⟨hx.1.mul hy.1, fun u => by
    rw [hx.1.theta_mul D hy.1 u, hx.2 u, hy.2 u, add_zero]⟩
  one_mem' := ⟨IsF.one, fun u => by simp⟩
  inv_mem' := fun {x} hx => ⟨hx.1.inv, fun u => by rw [hx.1.theta_inv D u, hx.2 u]⟩

theorem card_AltGrp_le (D : SpData ω V) : Nat.card (AltGrp ω V D) ≤ 8 := by
  classical
  obtain ⟨X, hX⟩ := Submodule.exists_isCompl V
  have hXdim : finrank (ZMod 2) X = 3 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hX
    have := D.finrank_W
    have := D.finrank_V
    omega
  let e := Module.finBasisOfFinrankEq (ZMod 2) X hXdim
  let f : AltGrp ω V D → (Fin 3 → ZMod 2) := fun x =>
    ![ω ((x : W ≃ₗ[ZMod 2] W) (e 0) - e 0) (e 1), ω ((x : W ≃ₗ[ZMod 2] W) (e 0) - e 0) (e 2),
      ω ((x : W ≃ₗ[ZMod 2] W) (e 1) - e 1) (e 2)]
  have hf : Function.Injective f := by
    intro x x' hxx'
    have hx := x.2
    have hx' := x'.2
    have hM : ∀ i j : Fin 3, ω ((x : W ≃ₗ[ZMod 2] W) (e i) - e i) (e j) =
        ω ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i) (e j) := by
      have h0 := congrFun hxx' 0
      have h1 := congrFun hxx' 1
      have h2 := congrFun hxx' 2
      simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
      have dg : ∀ i, ω ((x : W ≃ₗ[ZMod 2] W) (e i) - e i) (e i) = 0 := fun i => hx.2 _
      have dg' : ∀ i, ω ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i) (e i) = 0 := fun i => hx'.2 _
      have sy : ∀ i j, ω ((x : W ≃ₗ[ZMod 2] W) (e i) - e i) (e j) =
          ω ((x : W ≃ₗ[ZMod 2] W) (e j) - e j) (e i) := fun i j => hx.1.rel D _ _
      have sy' : ∀ i j, ω ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i) (e j) =
          ω ((x' : W ≃ₗ[ZMod 2] W) (e j) - e j) (e i) := fun i j => hx'.1.rel D _ _
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Fin.isValue] <;> first
        | rw [dg, dg']
        | exact h0
        | exact h1
        | exact h2
        | rw [sy, sy']; exact h0
        | rw [sy, sy']; exact h1
        | rw [sy, sy']; exact h2
    have hsum : ∀ w : W, ∃ v ∈ V, ∃ xw : X, w = v + (xw : W) := by
      intro w
      have hw : w ∈ V ⊔ X := by rw [hX.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨v, hv, xw, hxw, rfl⟩ := Submodule.mem_sup.mp hw
      exact ⟨v, hv, ⟨xw, hxw⟩, rfl⟩
    have hδ : ∀ i, (x : W ≃ₗ[ZMod 2] W) (e i) = (x' : W ≃ₗ[ZMod 2] W) (e i) := by
      intro i
      have haV := hx.1.sub_mem D (e i : W)
      have ha'V := hx'.1.sub_mem D (e i : W)
      have hδV : (x : W ≃ₗ[ZMod 2] W) (e i) - e i - ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i) ∈ V :=
        V.sub_mem haV ha'V
      have hψ : (LinearMap.comp (ω ((x : W ≃ₗ[ZMod 2] W) (e i) - e i -
          ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i))) X.subtype) = 0 := by
        refine e.ext fun j => ?_
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
        rw [map_sub ω, LinearMap.sub_apply, hM i j, sub_self]
      have hδ0 : ∀ w, ω ((x : W ≃ₗ[ZMod 2] W) (e i) - e i -
          ((x' : W ≃ₗ[ZMod 2] W) (e i) - e i)) w = 0 := by
        intro w
        obtain ⟨v, hv, xw, rfl⟩ := hsum w
        rw [map_add, D.iso _ hδV v hv, zero_add]
        exact LinearMap.congr_fun hψ xw
      have := D.eq_zero_of_forall hδ0
      have h2 : (x : W ≃ₗ[ZMod 2] W) (e i) - e i = (x' : W ≃ₗ[ZMod 2] W) (e i) - e i :=
        sub_eq_zero.mp this
      exact sub_left_injective h2
    refine Subtype.ext (LinearEquiv.ext fun u => ?_)
    obtain ⟨v, hv, xw, rfl⟩ := hsum u
    have hX1 : (LinearMap.comp ((x : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) X.subtype) =
        LinearMap.comp ((x' : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) X.subtype :=
      e.ext fun j => hδ j
    rw [map_add, map_add, hx.1.triv v hv, hx'.1.triv v hv]
    have := LinearMap.congr_fun hX1 xw
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at this
    rw [this]
  have hcard : Nat.card (Fin 3 → ZMod 2) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
    simp
  calc Nat.card (AltGrp ω V D) ≤ Nat.card (Fin 3 → ZMod 2) := Nat.card_le_card_of_injective f hf
    _ = 8 := hcard

instance : Finite (W ≃ₗ[ZMod 2] W) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

theorem AltGrp.conj_mem (D : SpData ω V) {γ x : W ≃ₗ[ZMod 2] W}
    (hγ : ∀ u v, ω (γ u) (γ v) = ω u v) (hγV : ∀ v ∈ V, γ v ∈ V)
    (hx : x ∈ AltGrp ω V D) : γ * x * γ⁻¹ ∈ AltGrp ω V D :=
  ⟨hx.1.conj hγ hγV (fun v hv => symm_mem_of_mem hγV hv), fun u => by
    rw [hx.1.theta_conj D hγ u]
    exact hx.2 _⟩

theorem eq_alt_of_card (D : SpData ω V) {Γ0 : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hle : Γ0 ≤ AltGrp ω V D) (hcard : 8 ≤ Nat.card Γ0) : Γ0 = AltGrp ω V D :=
  Subgroup.eq_of_le_of_card_ge hle ((card_AltGrp_le D).trans hcard)

end Alt

section PointStab

variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}
  {Γ : Subgroup (W ≃ₗ[ZMod 2] W)}

theorem eq_one_of_forall (D : SpData ω V) {x : W ≃ₗ[ZMod 2] W}
    (hx : ∀ b ∈ V, b ≠ 0 → ∀ u, ω u b = 0 → x u - u ∈ Submodule.span (ZMod 2) {b}) :
    x = 1 := by
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨b, hb0, hbu⟩ := exists_ne_zero_mem_ker D.finrank_V (LinearMap.comp (ω u) V.subtype)
  have hb1 : (b : W) ≠ 0 := fun h => hb0 (Subtype.ext h)
  obtain ⟨φb, hφb, -⟩ := exists_dual_of_notMem (p := (⊥ : Submodule (ZMod 2) V)) (x := b)
    (by simpa using hb0)
  obtain ⟨b', hb'0, hb'u, hb'φ⟩ := exists_ne_zero_mem_ker₂ D.finrank_V
    (LinearMap.comp (ω u) V.subtype) φb
  have h1 := hx b b.2 hb1 u hbu
  have h2 := hx b' b'.2 (fun h => hb'0 (Subtype.ext h)) u hb'u
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp h2
  rcases zmod2_cases r with rfl | rfl
  · rw [zero_smul] at hr
    have : x u = u := (sub_eq_zero.mp hr.symm)
    simpa using this
  · exfalso
    rw [one_smul] at hr
    rcases zmod2_cases r' with rfl | rfl
    · rw [zero_smul] at hr'
      exact hb1 (hr.trans hr'.symm)
    · rw [one_smul] at hr'
      have hbb : (b : W) = b' := hr.trans hr'.symm
      have hbb' : b = b' := Subtype.ext hbb
      rw [← hbb'] at hb'φ
      rw [hφb] at hb'φ
      exact one_ne_zero hb'φ

theorem eq_bot_of_normal (D : SpData ω V) (hΓ : IsGamma ω V Γ) {a : W} (haV : a ∈ V)
    (ha0 : a ≠ 0) {Λ : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hΛc : ∀ x ∈ Λ, ∀ u, ω u a = 0 → x u - u ∈ Submodule.span (ZMod 2) {a})
    (hΛn : ∀ γ ∈ Γ, ∀ x ∈ Λ, γ * x * γ⁻¹ ∈ Λ) : Λ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall D fun b hbV hb0 u hbu => ?_
  obtain ⟨h, hh⟩ := exists_apply_eq D.finrank_V (x := (⟨a, haV⟩ : V)) (y := (⟨b, hbV⟩ : V))
    (fun h => ha0 (congrArg Subtype.val h)) (fun h => hb0 (congrArg Subtype.val h))
  obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
  have hγa : γ a = b := by
    have := hγh ⟨a, haV⟩
    rw [hh] at this
    exact this
  have hx' : γ⁻¹ * x * γ ∈ Λ := by
    have := hΛn γ⁻¹ (Γ.inv_mem hγ) x hx
    simpa using this
  have hωu : ω (γ.symm u) a = 0 := by
    rw [hΓ.isom_symm hγ, hγa]
    exact hbu
  have h1 := hΛc _ hx' (γ.symm u) hωu
  have e : (γ⁻¹ * x * γ) (γ.symm u) - γ.symm u = γ.symm (x u - u) := by
    rw [map_sub]
    show γ.symm (x (γ (γ.symm u))) - γ.symm u = γ.symm (x u) - γ.symm u
    rw [LinearEquiv.apply_symm_apply]
  rw [e] at h1
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h1
  have : x u - u = r • b := by
    have := congrArg γ hr
    rw [map_smul, hγa, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)

theorem eq_transvection (D : SpData ω V) {a : W} (ha0 : a ≠ 0) {x : W ≃ₗ[ZMod 2] W}
    (hx : ∀ u v, ω (x u) (x v) = ω u v)
    (hxa : ∀ u, x u - u ∈ Submodule.span (ZMod 2) {a}) :
    ∃ κ : ZMod 2, ∀ u, x u = u + (κ * ω u a) • a := by
  choose ξ hξ using fun u => Submodule.mem_span_singleton.mp (hxa u)
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : W, ω u₁ a = 1 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    refine D.nondeg.2 a fun x => ?_
    rcases zmod2_cases (ω x a) with h | h
    · exact h
    · exact absurd h (hcon x)
  have hxu : ∀ w, x w = w + ξ w • a := fun w => by rw [hξ w]; abel
  refine ⟨ξ u₁, fun u => ?_⟩
  have h := hx u u₁
  rw [hxu u, hxu u₁] at h
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    D.alt a] at h
  rw [D.symm a u₁, hu₁] at h
  have h' : ξ u = ξ u₁ * ω u a := by
    have h2 : ξ u₁ * ω u a + ξ u = 0 := by linear_combination h
    exact (zmod2_add_eq_zero h2).symm
  rw [hxu u, h']

theorem eq_perp_of_stable (D : SpData ω V) (hΓ : IsGamma ω V Γ) {a : W} (haV : a ∈ V)
    (ha0 : a ≠ 0) {Dsub : Submodule (ZMod 2) W} (hVD : V ≤ Dsub)
    (hdim : finrank (ZMod 2) Dsub = 5)
    (hst : ∀ γ ∈ Γ, γ a = a → ∀ d ∈ Dsub, γ d ∈ Dsub) (u : W) :
    u ∈ Dsub ↔ ω u a = 0 := by
  have hperp_dim : finrank (ZMod 2) (ω.orthogonal Dsub) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal D.nondeg, D.finrank_W, hdim]
  have hperp_ne : ω.orthogonal Dsub ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hperp_dim
    omega
  obtain ⟨d₀, hd₀, hd₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
  have hd₀V : d₀ ∈ V := by
    rw [← D.perp_eq]
    exact LinearMap.BilinForm.orthogonal_le hVD hd₀
  have hDeq : ∀ w, w ∈ Dsub ↔ ω d₀ w = 0 := by
    have hle : Dsub ≤ ω.orthogonal (Submodule.span (ZMod 2) {d₀}) := by
      intro w hw n hn
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have := LinearMap.BilinForm.mem_orthogonal_iff.mp hd₀ w hw
      rw [map_smul, LinearMap.smul_apply, D.symm, this, smul_zero]
    have hfin : finrank (ZMod 2) (ω.orthogonal (Submodule.span (ZMod 2) {d₀})) ≤
        finrank (ZMod 2) Dsub := by
      rw [LinearMap.BilinForm.finrank_orthogonal D.nondeg, D.finrank_W, hdim,
        finrank_span_singleton hd₀0]
    have heq := Submodule.eq_of_le_of_finrank_le hle hfin
    intro w
    rw [heq]
    constructor
    · intro hw
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp hw d₀ (Submodule.mem_span_singleton_self d₀)
    · intro hw
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [map_smul, LinearMap.smul_apply, hw, smul_zero]
  have hd₀a : d₀ = a := by
    by_contra hne
    have hxs : (⟨d₀, hd₀V⟩ : V) ∉ Submodule.span (ZMod 2) {(⟨a, haV⟩ : V)} := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
      have hr' : r • a = d₀ := congrArg Subtype.val hr
      rcases zmod2_cases r with rfl | rfl
      · rw [zero_smul] at hr'
        exact hd₀0 hr'.symm
      · rw [one_smul] at hr'
        exact hne hr'.symm
    have hys : (⟨d₀ + a, V.add_mem hd₀V haV⟩ : V) ∉
        Submodule.span (ZMod 2) {(⟨a, haV⟩ : V)} := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
      have hr' : r • a = d₀ + a := congrArg Subtype.val hr
      rcases zmod2_cases r with rfl | rfl
      · rw [zero_smul] at hr'
        exact hne (vec_eq_of_add_eq_zero hr'.symm)
      · rw [one_smul] at hr'
        exact hd₀0 (add_eq_right.mp hr'.symm)
    obtain ⟨h, hha, hhd⟩ := exists_fix_apply_eq D.finrank_V hxs hys
    obtain ⟨γ, hγ, hγh⟩ := hΓ.onto h
    have hγa : γ a = a := by
      have := hγh ⟨a, haV⟩
      rw [hha] at this
      exact this
    have hγd : γ d₀ = d₀ + a := by
      have := hγh ⟨d₀, hd₀V⟩
      rw [hhd] at this
      exact this
    have hγs : γ.symm d₀ = d₀ + a := by
      rw [LinearEquiv.symm_apply_eq, map_add, hγd, hγa, add_assoc, vec_add_self, add_zero]
    have key : ∀ d, ω d₀ d = 0 → ω a d = 0 := by
      intro d hd
      have h1 := hst γ hγ hγa d ((hDeq d).mpr hd)
      rw [hDeq, ← hΓ.isom_symm hγ d₀ d, hγs, map_add, LinearMap.add_apply, hd, zero_add] at h1
      exact h1
    obtain ⟨u₁, hu₁⟩ : ∃ u₁ : W, ω a u₁ = 1 := by
      by_contra hcon
      push Not at hcon
      apply ha0
      refine D.eq_zero_of_forall fun x => ?_
      rcases zmod2_cases (ω a x) with h | h
      · exact h
      · exact absurd h (hcon x)
    have hd₀u₁ : ω d₀ u₁ = 1 := by
      rcases zmod2_cases (ω d₀ u₁) with h | h
      · rw [key u₁ h] at hu₁
        exact absurd hu₁ zero_ne_one
      · exact h
    have hforall : ∀ w, ω a w = ω d₀ w := by
      intro w
      have h0 : ω d₀ (w + ω d₀ w • u₁) = 0 := by
        rw [map_add, map_smul, hd₀u₁, smul_eq_mul, mul_one]
        exact zmod2_add_self _
      have h1 := key _ h0
      rw [map_add, map_smul, hu₁, smul_eq_mul, mul_one] at h1
      exact (zmod2_add_eq_zero h1)
    apply hne
    have : a - d₀ = 0 := D.eq_zero_of_forall fun w => by
      rw [map_sub, LinearMap.sub_apply, hforall w, sub_self]
    exact (sub_eq_zero.mp this).symm
  rw [hDeq, hd₀a, D.symm]

theorem sub_mem_span_of_all {a u₁ : W} (hu₁ : ω u₁ a = 1) {y : W ≃ₗ[ZMod 2] W}
    (hy : ∀ w, ω w a = 0 → y w - w ∈ Submodule.span (ZMod 2) {a})
    (hy1 : y u₁ - u₁ ∈ Submodule.span (ZMod 2) {a}) :
    ∀ w, y w - w ∈ Submodule.span (ZMod 2) {a} := by
  intro w
  set w' := w + ω w a • u₁ with hw'
  have hw'a : ω w' a = 0 := by
    rw [hw', map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hu₁, smul_eq_mul,
      mul_one]
    exact zmod2_add_self _
  have e2 : w = w' + ω w a • u₁ := by
    rw [hw', add_assoc, vec_add_self (ω w a • u₁), add_zero]
  have e1 : y w = y w' + ω w a • y u₁ := by
    have := congrArg y e2
    rw [map_add, map_smul] at this
    exact this
  have : y w - w = ω w a • (y u₁ - u₁) + (y w' - w') := by
    rw [smul_sub]
    nth_rewrite 2 [e2]
    rw [e1]
    abel
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hy1) (hy w' hw'a)

theorem eq_one_of_mem_span (D : SpData ω V) {a : W} (ha0 : a ≠ 0)
    {Λ : Subgroup (W ≃ₗ[ZMod 2] W)} (hiso : ∀ x ∈ Λ, ∀ u v, ω (x u) (x v) = ω u v)
    (hτ : ∀ x ∈ Λ, ¬ ∀ u, x u = u + ω u a • a) {y : W ≃ₗ[ZMod 2] W} (hy : y ∈ Λ)
    (hya : ∀ u, y u - u ∈ Submodule.span (ZMod 2) {a}) : y = 1 := by
  obtain ⟨κ, hκ⟩ := eq_transvection D ha0 (hiso y hy) hya
  rcases zmod2_cases κ with rfl | rfl
  · refine LinearEquiv.ext fun u => ?_
    rw [hκ u, zero_mul, zero_smul, add_zero]
    rfl
  · exact absurd (fun u => by rw [hκ u, one_mul]) (hτ y hy)

theorem theta_eq_mul {a u₁ : W} (D : SpData ω V) (hu₁ : ω u₁ a = 1)
    {y : W ≃ₗ[ZMod 2] W} (hy : ∀ w, ω w a = 0 → y w - w ∈ Submodule.span (ZMod 2) {a})
    (hyF : IsF ω V y) (u : W) : ω (y u - u) u = ω u a * ω (y u₁ - u₁) u₁ := by
  set c := ω u a with hc
  have hu' : ω (u + c • u₁) a = 0 := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hu₁, smul_eq_mul, mul_one]
    exact zmod2_add_self _
  have h3 : ω (y (u + c • u₁) - (u + c • u₁)) (u + c • u₁) = 0 := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hy (u + c • u₁) hu')
    rw [← hr, map_smul, LinearMap.smul_apply, D.symm a _, hu', smul_zero]
  have h1 := hyF.theta_add D (u + c • u₁) (c • u₁)
  have h2 := hyF.theta_smul D c u₁
  have e : u + c • u₁ + c • u₁ = u := by rw [add_assoc, vec_add_self, add_zero]
  rw [e, h3, h2, zero_add, smul_eq_mul] at h1
  exact h1

theorem alt_of_Lambda (D : SpData ω V) (hΓ : IsGamma ω V Γ) {a : W} (haV : a ∈ V) (ha0 : a ≠ 0)
    {Λ : Subgroup (W ≃ₗ[ZMod 2] W)} (hΛΓ : Λ ≤ Γ)
    (hΛc : ∀ x ∈ Λ, ∀ u, ω u a = 0 → x u - u ∈ Submodule.span (ZMod 2) {a})
    (hΛn : ∀ γ ∈ Γ, γ a = a → ∀ x ∈ Λ, γ * x * γ⁻¹ ∈ Λ)
    (hτ : ∀ x ∈ Λ, ¬ ∀ u, x u = u + ω u a • a)
    {x : W ≃ₗ[ZMod 2] W} (hx : x ∈ Λ) (hxV : ∀ v ∈ V, x v = v) (u : W) :
    ω (x u - u) u = 0 := by
  have hiso : ∀ y ∈ Λ, ∀ u v, ω (y u) (y v) = ω u v := fun y hy => hΓ.isom y (hΛΓ hy)
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : W, ω u₁ a = 1 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    refine D.nondeg.2 a fun x => ?_
    rcases zmod2_cases (ω x a) with h | h
    · exact h
    · exact absurd h (hcon x)
  have hxF : IsF ω V x := ⟨hiso x hx, hxV⟩
  suffices hκ : ω (x u₁ - u₁) u₁ = 0 by
    rw [theta_eq_mul D hu₁ (hΛc x hx) hxF u, hκ, mul_zero]
  have hc₀V : x u₁ - u₁ ∈ V := hxF.sub_mem D u₁
  by_cases hspan : x u₁ - u₁ ∈ Submodule.span (ZMod 2) {a}
  · have hxa := sub_mem_span_of_all hu₁ (hΛc x hx) hspan
    have hx1 := eq_one_of_mem_span D ha0 hiso hτ hx hxa
    rw [hx1]
    show ω (u₁ - u₁) u₁ = 0
    rw [sub_self, map_zero, LinearMap.zero_apply]
  · set c₀ := x u₁ - u₁ with hc₀
    set aV : V := ⟨a, haV⟩ with haVdef
    set c₀V : V := ⟨c₀, hc₀V⟩ with hc₀Vdef
    have hc₀' : c₀V ∉ Submodule.span (ZMod 2) {aV} := by
      intro h
      apply hspan
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
      exact Submodule.mem_span_singleton.mpr ⟨r, congrArg Subtype.val hr⟩
    obtain ⟨c₁, hc₁⟩ := exists_notMem_span_pair D.finrank_V aV c₀V
    have hc₁a : c₁ ∉ Submodule.span (ZMod 2) {aV} := fun h =>
      hc₁ (Submodule.span_mono (by simp) h)
    have hc₂a : c₀V + c₁ ∉ Submodule.span (ZMod 2) {aV} := by
      intro h
      apply hc₁
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
      have : c₁ = r • aV + c₀V := by
        calc c₁ = (c₀V + c₁) + c₀V := by rw [add_comm c₀V c₁, add_assoc, vec_add_self, add_zero]
          _ = r • aV + c₀V := by rw [← hr]
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
    obtain ⟨h₁, hh₁a, hh₁c⟩ := exists_fix_apply_eq D.finrank_V hc₀' hc₁a
    obtain ⟨h₂, hh₂a, hh₂c⟩ := exists_fix_apply_eq D.finrank_V hc₀' hc₂a
    obtain ⟨γ₁, hγ₁, hγ₁h⟩ := hΓ.onto h₁
    obtain ⟨γ₂, hγ₂, hγ₂h⟩ := hΓ.onto h₂
    have hγ₁a : γ₁ a = a := by
      have := hγ₁h aV
      rw [hh₁a] at this
      exact this
    have hγ₂a : γ₂ a = a := by
      have := hγ₂h aV
      rw [hh₂a] at this
      exact this
    have hγ₁c : γ₁ c₀ = c₁ := by
      have := hγ₁h c₀V
      rw [hh₁c] at this
      exact this
    have hγ₂c : γ₂ c₀ = c₀ + c₁ := by
      have := hγ₂h c₀V
      rw [hh₂c] at this
      exact this
    have hconjF : ∀ γ ∈ Γ, IsF ω V (γ * x * γ⁻¹) := fun γ hγ =>
      hxF.conj (hΓ.isom γ hγ) (hΓ.stabV γ hγ) (fun v hv => hΓ.stabV_symm hγ hv)
    have hν : ∀ γ ∈ Γ, γ a = a → ∃ r : ZMod 2, (γ * x * γ⁻¹) u₁ - u₁ = γ c₀ + r • a := by
      intro γ hγ hγa
      set h := γ.symm u₁ + u₁ with hh
      have hha : ω h a = 0 := by
        rw [hh, map_add, LinearMap.add_apply, hΓ.isom_symm hγ, hγa, hu₁]
        exact zmod2_add_self _
      have hγu₁ : γ.symm u₁ = u₁ + h := by
        rw [hh, add_comm (γ.symm u₁) u₁, ← add_assoc, vec_add_self, zero_add]
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hΛc x hx h hha)
      refine ⟨r, ?_⟩
      have e1 : (γ * x * γ⁻¹) u₁ - u₁ = γ (x (γ.symm u₁) - γ.symm u₁) := by
        rw [map_sub]
        show γ (x (γ.symm u₁)) - u₁ = γ (x (γ.symm u₁)) - γ (γ.symm u₁)
        rw [γ.apply_symm_apply]
      have e2 : x (u₁ + h) - (u₁ + h) = c₀ + r • a := by
        rw [hr, map_add, hc₀]
        abel
      rw [e1, hγu₁, e2, map_add, map_smul, hγa]
    have hκeq : ∀ γ ∈ Γ, γ a = a →
        ω ((γ * x * γ⁻¹) u₁ - u₁) u₁ = ω (x u₁ - u₁) u₁ := by
      intro γ hγ hγa
      rw [hxF.theta_conj D (hΓ.isom γ hγ) u₁, theta_eq_mul D hu₁ (hΛc x hx) hxF (γ.symm u₁),
        hΓ.isom_symm hγ, hγa, hu₁, one_mul]
    have hx₁ : γ₁ * x * γ₁⁻¹ ∈ Λ := hΛn γ₁ hγ₁ hγ₁a x hx
    have hx₂ : γ₂ * x * γ₂⁻¹ ∈ Λ := hΛn γ₂ hγ₂ hγ₂a x hx
    obtain ⟨r₁, hr₁⟩ := hν γ₁ hγ₁ hγ₁a
    obtain ⟨r₂, hr₂⟩ := hν γ₂ hγ₂ hγ₂a
    have hy : x * (γ₁ * x * γ₁⁻¹) * (γ₂ * x * γ₂⁻¹) ∈ Λ :=
      Λ.mul_mem (Λ.mul_mem hx hx₁) hx₂
    have hyF : IsF ω V (x * (γ₁ * x * γ₁⁻¹) * (γ₂ * x * γ₂⁻¹)) :=
      (hxF.mul (hconjF γ₁ hγ₁)).mul (hconjF γ₂ hγ₂)
    have hy1 : (x * (γ₁ * x * γ₁⁻¹) * (γ₂ * x * γ₂⁻¹)) u₁ - u₁ ∈
        Submodule.span (ZMod 2) {a} := by
      rw [(hxF.mul (hconjF γ₁ hγ₁)).mul_sub D (hconjF γ₂ hγ₂), hxF.mul_sub D (hconjF γ₁ hγ₁),
        hr₁, hr₂, hγ₁c, hγ₂c]
      have : x u₁ - u₁ + (c₁ + r₁ • a) + (c₀ + c₁ + r₂ • a) =
          (c₀ + c₀) + (c₁ + c₁) + (r₁ • a + r₂ • a) := by
        rw [← hc₀]
        abel
      rw [this, vec_add_self c₀, vec_add_self (c₁ : W), zero_add, zero_add, ← add_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    have hya := sub_mem_span_of_all hu₁ (hΛc _ hy) hy1
    have hy1' := eq_one_of_mem_span D ha0 hiso hτ hy hya
    have h0 : ω ((x * (γ₁ * x * γ₁⁻¹) * (γ₂ * x * γ₂⁻¹)) u₁ - u₁) u₁ = 0 := by
      rw [hy1']
      show ω (u₁ - u₁) u₁ = 0
      rw [sub_self, map_zero, LinearMap.zero_apply]
    rw [(hxF.mul (hconjF γ₁ hγ₁)).theta_mul D (hconjF γ₂ hγ₂), hxF.theta_mul D (hconjF γ₁ hγ₁),
      hκeq γ₁ hγ₁ hγ₁a, hκeq γ₂ hγ₂ hγ₂a] at h0
    have hs := zmod2_add_self (ω (x u₁ - u₁) u₁)
    linear_combination h0 - hs

end PointStab

end CFSG.GF2Type.Smith1979.Case2.Sp
