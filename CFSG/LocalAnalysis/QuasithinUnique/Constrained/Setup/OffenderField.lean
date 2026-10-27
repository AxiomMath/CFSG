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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LittleWedderburn
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open Module TensorProduct

universe u v

section

variable {k : Type*} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

@[expose] def toEnd (H : Subgroup (W ≃ₗ[k] W)) : H →* Module.End k W where
  toFun h := ((h : W ≃ₗ[k] W) : W →ₗ[k] W)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[expose] def spanAlg (H : Subgroup (W ≃ₗ[k] W)) : Subalgebra k (Module.End k W) :=
  Algebra.adjoin k (Set.range (toEnd H))

theorem mem_spanAlg_of_mem {H : Subgroup (W ≃ₗ[k] W)} {h : W ≃ₗ[k] W} (hh : h ∈ H) :
    (h : W →ₗ[k] W) ∈ spanAlg H :=
  Algebra.subset_adjoin ⟨⟨h, hh⟩, rfl⟩

theorem spanAlg_toSubmodule (H : Subgroup (W ≃ₗ[k] W)) :
    (spanAlg H).toSubmodule = Submodule.span k (Set.range (toEnd H)) := by
  rw [spanAlg, Algebra.adjoin_eq_span]
  congr 1
  have h : Submonoid.closure (Set.range ⇑(toEnd H)) = MonoidHom.mrange (toEnd H) := by
    apply le_antisymm
    · exact Submonoid.closure_le.2 (fun x hx => hx)
    · rintro _ ⟨h, rfl⟩; exact Submonoid.subset_closure ⟨h, rfl⟩
  rw [h]
  exact MonoidHom.coe_mrange _

abbrev EndF (H : Subgroup (W ≃ₗ[k] W)) := Module.End (spanAlg H) W

abbrev IsIrrAct (H : Subgroup (W ≃ₗ[k] W)) : Prop :=
  ∀ U : Submodule k W, (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤

theorem comm_spanAlg {H : Subgroup (W ≃ₗ[k] W)} {f : Module.End k W}
    (hf : ∀ h ∈ H, ∀ w, f (h w) = h (f w)) {r : Module.End k W} (hr : r ∈ spanAlg H) :
    ∀ w, f (r w) = r (f w) := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨h, rfl⟩ := hx; intro w; exact hf h h.2 w
  | algebraMap c => intro w; simp
  | add x y _ _ hx hy => intro w; simp [hx, hy]
  | mul x y _ _ hx hy => intro w; simp [Module.End.mul_apply, hx, hy]

theorem commutant_iff {H : Subgroup (W ≃ₗ[k] W)} (f : Module.End k W) :
    (∀ h ∈ H, ∀ w, f (h w) = h (f w)) ↔ ∃ c : EndF H, ∀ w, f w = c • w := by
  constructor
  · intro hf
    refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun r w => ?_ }, fun w => rfl⟩
    exact comm_spanAlg hf r.2 w
  · rintro ⟨c, hc⟩ h hh w
    have := c.map_smul (⟨(h : W →ₗ[k] W), mem_spanAlg_of_mem hh⟩ : spanAlg H) w
    rw [hc, hc]
    exact this

theorem span_iff {H : Subgroup (W ≃ₗ[k] W)} [Finite W] [IsSimpleModule (spanAlg H) W]
    (f : Module.End k W) :
    f ∈ Submodule.span k (Set.range (toEnd H)) ↔ ∀ (c : EndF H) (w : W), f (c • w) = c • f w := by
  rw [← spanAlg_toSubmodule]
  constructor
  · intro hf c w
    have := c.map_smul (⟨f, hf⟩ : spanAlg H) w
    exact this.symm
  · intro hf
    have : Fintype W := Fintype.ofFinite W
    let f' : Module.End (EndF H) W :=
      { toFun := f, map_add' := f.map_add, map_smul' := fun c w => hf c w }
    obtain ⟨r, hr⟩ := jacobson_density f' Finset.univ
    have : f = (r : Module.End k W) := LinearMap.ext fun w => hr w (Finset.mem_univ w)
    rw [this]
    exact r.2

theorem isSimpleModule_spanAlg [Nontrivial W] (H : Subgroup (W ≃ₗ[k] W)) (hirr : IsIrrAct H) :
    IsSimpleModule (spanAlg H) W := by
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun U => ?_ }
  have hU : ∀ h ∈ H, ∀ u ∈ U.restrictScalars k, h u ∈ U.restrictScalars k := fun h hh u hu =>
    U.smul_mem (⟨(h : W →ₗ[k] W), mem_spanAlg_of_mem hh⟩ : spanAlg H) hu
  rcases hirr _ hU with h | h
  · left
    exact Submodule.restrictScalars_injective k (spanAlg H) W (by rw [h]; rfl)
  · right
    exact Submodule.restrictScalars_injective k (spanAlg H) W (by rw [h]; rfl)

instance instFiniteEndF [Finite W] (H : Subgroup (W ≃ₗ[k] W)) : Finite (EndF H) :=
  Finite.of_injective (fun f : EndF H => (f : W → W)) DFunLike.coe_injective

noncomputable instance endFFieldInst [Nontrivial W] [Finite W] (H : Subgroup (W ≃ₗ[k] W))
    [Fact (IsIrrAct H)] : Field (EndF H) := by
  classical
  haveI := isSimpleModule_spanAlg H Fact.out
  exact littleWedderburn _

section Abs

variable {H : Subgroup (W ≃ₗ[k] W)} {F : Type u} [Field F] [Module F W] [Algebra k F]
  [IsScalarTower k F W]

theorem absIrr_core {E : Type v} [Field E] [Algebra F E]
    (hspan : ∀ g : W →ₗ[F] W, (g.restrictScalars k) ∈ Submodule.span k (Set.range (toEnd H)))
    (hH : ∀ h ∈ H, ∃ g : W →ₗ[F] W, (∀ w, g w = h w))
    (U : Submodule E (E ⊗[F] W))
    (hU : ∀ h ∈ H, ∀ g : W →ₗ[F] W, (∀ w, g w = h w) → ∀ u ∈ U, g.baseChange E u ∈ U)
    (g : W →ₗ[F] W) : ∀ u ∈ U, g.baseChange E u ∈ U := by
  have key : ∀ f ∈ Submodule.span k (Set.range (toEnd H)), ∃ g : W →ₗ[F] W,
      (∀ w, g w = f w) ∧ ∀ u ∈ U, g.baseChange E u ∈ U := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      obtain ⟨g, hg⟩ := hH h h.2
      exact ⟨g, hg, hU h h.2 g hg⟩
    | zero => exact ⟨0, fun w => rfl, fun u _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨g₁, h₁, hu₁⟩ := hx
      obtain ⟨g₂, h₂, hu₂⟩ := hy
      refine ⟨g₁ + g₂, fun w => by simp [h₁, h₂], fun u hu => ?_⟩
      rw [LinearMap.baseChange_add]
      exact U.add_mem (hu₁ u hu) (hu₂ u hu)
    | smul c x _ hx =>
      obtain ⟨g₁, h₁, hu₁⟩ := hx
      refine ⟨(algebraMap k F c) • g₁, fun w => by simp [h₁, algebraMap_smul], fun u hu => ?_⟩
      rw [LinearMap.baseChange_smul]
      have := U.smul_mem (algebraMap F E (algebraMap k F c)) (hu₁ u hu)
      simpa [algebraMap_smul] using this
  obtain ⟨g', hg', hu'⟩ := key _ (hspan g)
  have : g' = g := LinearMap.ext fun w => hg' w
  rw [this] at hu'
  exact hu'

end Abs

section Abs2

variable {F : Type u} [Field F] {W : Type u} [AddCommGroup W] [Module F W] [Module.Finite F W]
variable {E : Type v} [Field E] [Algebra F E]

theorem eq_bot_or_top_of_invariant (U : Submodule E (E ⊗[F] W))
    (hall : ∀ g : W →ₗ[F] W, ∀ u ∈ U, g.baseChange E u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨u, huU, hu0⟩ := (Submodule.ne_bot_iff U).1 hU
  let b := Module.finBasis F W
  let bE := Algebra.TensorProduct.basis E b
  have hbE : ∀ l, bE l = (1 : E) ⊗ₜ[F] (b l) := fun l => by
    simp [bE, Algebra.TensorProduct.basis_apply]
  obtain ⟨j, hj⟩ : ∃ j, bE.repr u j ≠ 0 := by
    by_contra h
    apply hu0
    have h' : ∀ j, bE.repr u j = 0 := fun j => by_contra (fun hj => h ⟨j, hj⟩)
    have : bE.repr u = 0 := by ext l; simpa using h' l
    simpa using this
  let e : Fin (finrank F W) → Fin (finrank F W) → W →ₗ[F] W :=
    fun i j => (b.coord j).smulRight (b i)
  have he : ∀ i j l, (e i j).baseChange E (bE l) = if l = j then bE i else 0 := by
    intro i j l
    rw [hbE, LinearMap.baseChange_tmul]
    by_cases hlj : l = j
    · subst hlj
      simp [e, hbE]
    · simp [e, hlj]
  have hmem : ∀ i, bE i ∈ U := by
    intro i
    have h1 := hall (e i j) u huU
    have h2 : (e i j).baseChange E u = bE.repr u j • bE i := by
      conv_lhs => rw [← bE.sum_repr u]
      rw [map_sum, Finset.sum_eq_single j]
      · rw [map_smul, he]; simp
      · intro l _ hlj
        rw [map_smul, he]; simp [hlj]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [h2] at h1
    have := U.smul_mem (bE.repr u j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at this
  rw [eq_top_iff, ← bE.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hmem i

end Abs2

theorem gl_inv_apply_apply (g : W ≃ₗ[k] W) (x : W) : g⁻¹ (g x) = x := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem gl_apply_inv_apply (g : W ≃ₗ[k] W) (x : W) : g (g⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

theorem conj_mem_spanAlg {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) {r : Module.End k W}
    (hr : r ∈ spanAlg H) :
    ((b : W →ₗ[k] W) * r * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W)) ∈ spanAlg H := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    have hbh : b * (h : W ≃ₗ[k] W) * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hb h).1 h.2
    have e : (b : W →ₗ[k] W) * toEnd H h * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W) =
        ((b * (h : W ≃ₗ[k] W) * b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W) := by ext w; rfl
    rw [e]; exact mem_spanAlg_of_mem hbh
  | algebraMap c =>
    have : (b : W →ₗ[k] W) * (algebraMap k (Module.End k W) c) * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W)
        = algebraMap k (Module.End k W) c := by
      ext w
      simp [Module.End.mul_apply]
    rw [this]; exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have : (b : W →ₗ[k] W) * (x * y) * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W) =
        ((b : W →ₗ[k] W) * x * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W)) *
        ((b : W →ₗ[k] W) * y * ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W)) := by
      ext w
      simp [Module.End.mul_apply]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

@[expose] noncomputable def conjF {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) (c : EndF H) : EndF H where
  toFun w := b (c (b⁻¹ w))
  map_add' x y := by simp
  map_smul' r w := by
    have hb' : b⁻¹ ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W)) := Subgroup.inv_mem _ hb
    have hr' : ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W) * (r : Module.End k W) * (b : W →ₗ[k] W) ∈
        spanAlg H := by
      simpa using conj_mem_spanAlg hb' r.2
    have e1 : b⁻¹ (r • w) = (⟨_, hr'⟩ : spanAlg H) • (b⁻¹ w) := by
      show b⁻¹ ((r : Module.End k W) w) =
        ((b⁻¹ : W ≃ₗ[k] W) : W →ₗ[k] W) ((r : Module.End k W) (b (b⁻¹ w)))
      rw [gl_apply_inv_apply]
      rfl
    have e2 := c.map_smul (⟨_, hr'⟩ : spanAlg H) (b⁻¹ w)
    show b (c (b⁻¹ (r • w))) = r • b (c (b⁻¹ w))
    rw [e1, e2]
    show b (b⁻¹ ((r : Module.End k W) (b (c (b⁻¹ w))))) = _
    rw [gl_apply_inv_apply]
    rfl

theorem conjF_apply {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) (c : EndF H) (w : W) :
    conjF hb c w = b (c (b⁻¹ w)) := rfl

@[expose] noncomputable def conjAlgHom {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) : EndF H →ₐ[k] EndF H where
  toFun := conjF hb
  map_one' := by
    ext w
    show b (b⁻¹ w) = w
    exact gl_apply_inv_apply b w
  map_mul' c d := by
    ext w
    simp only [conjF_apply, Module.End.mul_apply, gl_inv_apply_apply]
  map_zero' := by ext w; simp [conjF_apply]
  map_add' c d := by ext w; simp [conjF_apply]
  commutes' a := by
    ext w
    simp [conjF_apply, Algebra.algebraMap_eq_smul_one]

theorem conjAlgHom_apply {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) (c : EndF H) (w : W) :
    conjAlgHom hb c w = b (c (b⁻¹ w)) := rfl

@[expose] noncomputable def conjAlgEquiv {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) : EndF H ≃ₐ[k] EndF H :=
  AlgEquiv.ofAlgHom (conjAlgHom hb) (conjAlgHom (Subgroup.inv_mem _ hb))
    (AlgHom.ext fun c => LinearMap.ext fun w => by
      simp only [AlgHom.comp_apply, conjAlgHom_apply, AlgHom.id_apply, inv_inv]
      rw [gl_apply_inv_apply, gl_apply_inv_apply])
    (AlgHom.ext fun c => LinearMap.ext fun w => by
      simp only [AlgHom.comp_apply, conjAlgHom_apply, AlgHom.id_apply, inv_inv]
      rw [gl_inv_apply_apply, gl_inv_apply_apply])

theorem conjAlgEquiv_smul {H : Subgroup (W ≃ₗ[k] W)} {b : W ≃ₗ[k] W}
    (hb : b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W))) (c : EndF H) (w : W) :
    b (c • w) = (conjAlgEquiv hb c) • (b w) := by
  show b (c w) = conjAlgHom hb c (b w)
  rw [conjAlgHom_apply, gl_inv_apply_apply]

theorem finite_irreducible_endomorphism_field_core [Nontrivial W] [Finite W]
    (H : Subgroup (W ≃ₗ[k] W)) (hirr : IsIrrAct H) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra k F) (_ : Module F W)
      (_ : IsScalarTower k F W),
      (∀ f : Module.End k W, (∀ h ∈ H, ∀ w, f (h w) = h (f w)) ↔ ∃ c : F, ∀ w, f w = c • w) ∧
      Module.Finite F W ∧
      (∀ f : Module.End k W, f ∈ Submodule.span k (Set.range (toEnd H)) ↔
        ∀ (c : F) (w : W), f (c • w) = c • f w) ∧
      (∀ b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W)),
        ∃ σ : F ≃ₐ[k] F, ∀ (c : F) (w : W), b (c • w) = σ c • b w) := by
  have : Fact (IsIrrAct H) := ⟨hirr⟩
  have := isSimpleModule_spanAlg H hirr
  exact ⟨EndF H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    commutant_iff, Module.Finite.of_finite, span_iff, fun b hb => ⟨conjAlgEquiv hb,
      conjAlgEquiv_smul hb⟩⟩

theorem finite_irreducible_endomorphism_field_density [Nontrivial W] [Finite W]
    (H : Subgroup (W ≃ₗ[k] W)) (hirr : IsIrrAct H) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra k F) (_ : Module F W)
      (_ : IsScalarTower k F W),
      (∀ f : Module.End k W, (∀ h ∈ H, ∀ w, f (h w) = h (f w)) ↔ ∃ c : F, ∀ w, f w = c • w) ∧
      Module.Finite F W ∧
      (∀ f : Module.End k W, f ∈ Submodule.span k (Set.range (toEnd H)) ↔
        ∀ (c : F) (w : W), f (c • w) = c • f w) ∧
      (∀ (E : Type v) (_ : Field E) (_ : Algebra F E) (U : Submodule E (E ⊗[F] W)),
        (∀ h ∈ H, ∀ g : W →ₗ[F] W, (∀ w, g w = h w) → ∀ u ∈ U, g.baseChange E u ∈ U) →
          U = ⊥ ∨ U = ⊤) ∧
      (∀ b ∈ Subgroup.normalizer (H : Set (W ≃ₗ[k] W)),
        ∃ σ : F ≃ₐ[k] F, ∀ (c : F) (w : W), b (c • w) = σ c • b w) := by
  have : Fact (IsIrrAct H) := ⟨hirr⟩
  have := isSimpleModule_spanAlg H hirr
  refine ⟨EndF H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    commutant_iff, Module.Finite.of_finite, span_iff, ?_, fun b hb => ⟨conjAlgEquiv hb,
      conjAlgEquiv_smul hb⟩⟩
  intro E _ _ U hU
  have : Module.Finite (EndF H) W := Module.Finite.of_finite
  have hspan : ∀ g : W →ₗ[EndF H] W, g.restrictScalars k ∈ Submodule.span k (Set.range (toEnd H)) :=
    fun g => (span_iff _).2 fun c w => g.map_smul c w
  have hH : ∀ h ∈ H, ∃ g : W →ₗ[EndF H] W, ∀ w, g w = h w := by
    intro h hh
    refine ⟨{ toFun := h, map_add' := h.map_add, map_smul' := fun c w => ?_ }, fun w => rfl⟩
    have := c.map_smul (⟨(h : W →ₗ[k] W), mem_spanAlg_of_mem hh⟩ : spanAlg H) w
    exact this.symm
  exact eq_bot_or_top_of_invariant U (absIrr_core hspan hH U hU)

end

end CFSG.QuasithinUnique.Setup.Offender
