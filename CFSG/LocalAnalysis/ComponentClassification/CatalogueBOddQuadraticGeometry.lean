module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticWitt
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddQuadratic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K]

theorem hyperbolicPairForm_polar (x y : K × K) :
    polar (hyperbolicPairForm K) x y = x.1 * y.2 + x.2 * y.1 := by
  simp only [polar, hyperbolicPairForm_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem hyperbolicSumForm_polar (m : ℕ) (x y : Fin m → K × K) :
    polar (hyperbolicSumForm K m) x y =
      ∑ i, ((x i).1 * (y i).2 + (x i).2 * (y i).1) := by
  rw [hyperbolicSumForm, QuadraticMap.Ring.polar_pi]
  simp only [hyperbolicPairForm_polar]

theorem hyperbolicSumForm_single_polar {m : ℕ} (i : Fin m) (x : K × K)
    (y : Fin m → K × K) :
    polar (hyperbolicSumForm K m) (Pi.single i x) y =
      x.1 * (y i).2 + x.2 * (y i).1 := by
  rw [hyperbolicSumForm_polar]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

section Transport

variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {m : ℕ}
  {Q : QuadraticForm K V} {R : QuadraticForm K W}
  (e : Q.IsometryEquiv ((hyperbolicSumForm K m).prod R))

private theorem polar_isometryEquiv {U U' : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup U'] [Module K U'] {Q' : QuadraticForm K U} {R' : QuadraticForm K U'}
    (f : Q'.IsometryEquiv R') (x y : U) :
    polar R' (f x) (f y) = polar Q' x y := by
  simp only [polar, ← map_add, f.map_app]

@[expose] def hyperbolicEmbedding : (Fin m → K × K) →ₗ[K] V :=
  e.symm.toLinearEquiv.toLinearMap.comp (LinearMap.inl K _ W)

theorem hyperbolicEmbedding_apply (x : Fin m → K × K) :
    hyperbolicEmbedding e x = e.symm (x, 0) := rfl

@[expose] def residualEmbedding : W →ₗ[K] V :=
  e.symm.toLinearEquiv.toLinearMap.comp (LinearMap.inr K (Fin m → K × K) W)

theorem residualEmbedding_apply (x : W) : residualEmbedding e x = e.symm (0, x) := rfl

theorem hyperbolicEmbedding_injective : Function.Injective (hyperbolicEmbedding e) :=
  e.symm.injective.comp fun _ _ h => congrArg Prod.fst h

theorem residualEmbedding_injective : Function.Injective (residualEmbedding e) :=
  e.symm.injective.comp fun _ _ h => congrArg Prod.snd h

theorem hyperbolicEmbedding_form (x : Fin m → K × K) :
    Q (hyperbolicEmbedding e x) = hyperbolicSumForm K m x := by
  rw [hyperbolicEmbedding_apply, e.symm.map_app, QuadraticMap.prod_apply, map_zero, add_zero]

theorem residualEmbedding_form (x : W) : Q (residualEmbedding e x) = R x := by
  rw [residualEmbedding_apply, e.symm.map_app, QuadraticMap.prod_apply, map_zero, zero_add]

@[expose] def planeEmbedding (i : Fin m) : (K × K) →ₗ[K] V :=
  (hyperbolicEmbedding e).comp (LinearMap.single K (fun _ : Fin m => K × K) i)

theorem planeEmbedding_apply (i : Fin m) (x : K × K) :
    planeEmbedding e i x = e.symm (Pi.single i x, 0) := rfl

theorem planeEmbedding_injective (i : Fin m) : Function.Injective (planeEmbedding e i) := by
  intro x y h
  have hxy := hyperbolicEmbedding_injective e h
  simpa using congrFun hxy i

theorem planeEmbedding_form (i : Fin m) (x : K × K) :
    Q (planeEmbedding e i x) = x.1 * x.2 := by
  change Q (hyperbolicEmbedding e (Pi.single i x)) = _
  rw [hyperbolicEmbedding_form, hyperbolicSumForm, QuadraticMap.pi_apply_single,
    hyperbolicPairForm_apply]

theorem planeEmbedding_polar (i : Fin m) (x : K × K) (v : V) :
    polar Q (planeEmbedding e i x) v =
      x.1 * ((e v).1 i).2 + x.2 * ((e v).1 i).1 := by
  rw [← polar_isometryEquiv e, planeEmbedding_apply, e.apply_symm_apply,
    QuadraticMap.polar_prod, polar_zero_left, add_zero, hyperbolicSumForm_single_polar]

theorem planeEmbedding_polar_of_ne {i j : Fin m} (hij : i ≠ j) (x y : K × K) :
    polar Q (planeEmbedding e i x) (planeEmbedding e j y) = 0 := by
  rw [planeEmbedding_polar, planeEmbedding_apply, e.apply_symm_apply]
  simp [Pi.single_eq_of_ne hij]

@[expose] def originalHypPair (i : Fin m) : HypPair Q where
  e := planeEmbedding e i (1, 0)
  f := planeEmbedding e i (0, 1)
  Q_e := by rw [planeEmbedding_form]; simp
  Q_f := by rw [planeEmbedding_form]; simp
  polar_ef := by
    rw [planeEmbedding_polar, planeEmbedding_apply, e.apply_symm_apply]
    simp

theorem originalHypPair_e (i : Fin m) :
    (originalHypPair e i).e = e.symm (Pi.single i (1, 0), 0) := rfl

theorem originalHypPair_f (i : Fin m) :
    (originalHypPair e i).f = e.symm (Pi.single i (0, 1), 0) := rfl

theorem originalHypPair_orth {i j : Fin m} (hij : i ≠ j) :
    (originalHypPair e i).Orth (originalHypPair e j) where
  ee := planeEmbedding_polar_of_ne e hij _ _
  ef := planeEmbedding_polar_of_ne e hij _ _
  fe := planeEmbedding_polar_of_ne e hij _ _
  ff := planeEmbedding_polar_of_ne e hij _ _

@[expose] def hyperbolicSubspace : Submodule K V := (hyperbolicEmbedding e).range

@[expose] def residualSubspace : Submodule K V := (residualEmbedding e).range

@[expose] def planeSubspace (i : Fin m) : Submodule K V := (planeEmbedding e i).range

@[expose] def hyperbolicSubspaceEquiv :
    (hyperbolicSumForm K m).IsometryEquiv (Q.restrict (hyperbolicSubspace e)) where
  toLinearEquiv := LinearEquiv.ofInjective _ (hyperbolicEmbedding_injective e)
  map_app' x := hyperbolicEmbedding_form e x

@[expose] def residualSubspaceEquiv : R.IsometryEquiv (Q.restrict (residualSubspace e)) where
  toLinearEquiv := LinearEquiv.ofInjective _ (residualEmbedding_injective e)
  map_app' x := residualEmbedding_form e x

@[expose] def planeSubspaceEquiv (i : Fin m) :
    (hyperbolicPairForm K).IsometryEquiv (Q.restrict (planeSubspace e i)) where
  toLinearEquiv := LinearEquiv.ofInjective _ (planeEmbedding_injective e i)
  map_app' x := planeEmbedding_form e i x

theorem hyperbolicSubspace_finrank : Module.finrank K (hyperbolicSubspace e) = 2 * m := by
  rw [← (hyperbolicSubspaceEquiv e).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_self, Nat.mul_comm]

theorem residualSubspace_finrank :
    Module.finrank K (residualSubspace e) = Module.finrank K W :=
  (residualSubspaceEquiv e).toLinearEquiv.finrank_eq.symm

theorem planeSubspace_finrank (i : Fin m) : Module.finrank K (planeSubspace e i) = 2 := by
  rw [← (planeSubspaceEquiv e i).toLinearEquiv.finrank_eq]
  simp

theorem planeSubspace_eq_span (i : Fin m) :
    planeSubspace e i =
      Submodule.span K {(originalHypPair e i).e, (originalHypPair e i).f} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x = x.1 • (1, (0 : K)) + x.2 • (0, (1 : K)) := by
      ext <;> simp
    rw [hx, map_add, map_smul, map_smul]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [originalHypPair]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [originalHypPair]))
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨(1, 0), rfl⟩
    · exact ⟨(0, 1), rfl⟩

theorem hyperbolicSubspace_eq_iSup_planes :
    hyperbolicSubspace e = ⨆ i, planeSubspace e i := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [← LinearMap.sum_single_apply (fun _ : Fin m => K × K) x, map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i ⟨x i, rfl⟩
  · apply iSup_le
    intro i x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Pi.single i y, rfl⟩

theorem hyperbolic_residual_orthogonal {x y : V} (hx : x ∈ hyperbolicSubspace e)
    (hy : y ∈ residualSubspace e) : polar Q x y = 0 := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  rw [hyperbolicEmbedding_apply, residualEmbedding_apply, polar_isometryEquiv e.symm,
    QuadraticMap.polar_prod, polar_zero_right, polar_zero_left, add_zero]

theorem hyperbolic_residual_isCompl :
    IsCompl (hyperbolicSubspace e) (residualSubspace e) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hvH hvR
    obtain ⟨x, hx⟩ := hvH
    obtain ⟨y, hy⟩ := hvR
    have hxy : (x, (0 : W)) = (0, y) := by
      apply e.symm.injective
      exact hx.trans hy.symm
    have hx0 : x = 0 := congrArg Prod.fst hxy
    rw [← hx, hx0, map_zero]
  · rw [codisjoint_iff_le_sup]
    intro v _
    refine Submodule.mem_sup.mpr ⟨hyperbolicEmbedding e (e v).1, ?_,
      residualEmbedding e (e v).2, ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    rw [hyperbolicEmbedding_apply, residualEmbedding_apply, ← map_add]
    simp

theorem residualSubspace_eq_orthogonal :
    residualSubspace e = LinearMap.BilinForm.orthogonal Q.polarBilin
      (hyperbolicSubspace e) := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    exact hyperbolic_residual_orthogonal e hx hv
  · intro v hv
    have hcoords : (e v).1 = 0 := by
      funext i
      have he : planeEmbedding e i (1, 0) ∈ hyperbolicSubspace e :=
        ⟨Pi.single i (1, 0), rfl⟩
      have hf : planeEmbedding e i (0, 1) ∈ hyperbolicSubspace e :=
        ⟨Pi.single i (0, 1), rfl⟩
      have h1 := hv _ he
      have h2 := hv _ hf
      rw [polarBilin_apply_apply, planeEmbedding_polar] at h1 h2
      apply Prod.ext
      · simpa using h2
      · simpa using h1
    refine ⟨(e v).2, ?_⟩
    rw [residualEmbedding_apply, ← hcoords]
    exact e.symm_apply_apply v

theorem residualSubspace_eq_iInf_perp :
    residualSubspace e = ⨅ i, (originalHypPair e i).perp := by
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_iInf]
    intro i
    rw [HypPair.mem_perp]
    constructor
    · exact hyperbolic_residual_orthogonal e ⟨Pi.single i (1, 0), rfl⟩ hv
    · exact hyperbolic_residual_orthogonal e ⟨Pi.single i (0, 1), rfl⟩ hv
  · intro hv
    have hcoords : (e v).1 = 0 := by
      funext i
      have hi : v ∈ (originalHypPair e i).perp := by
        exact (show ∀ j, v ∈ (originalHypPair e j).perp from by simpa using hv) i
      rw [HypPair.mem_perp] at hi
      have h1 := hi.1
      have h2 := hi.2
      change polar Q (planeEmbedding e i (1, 0)) v = 0 at h1
      change polar Q (planeEmbedding e i (0, 1)) v = 0 at h2
      rw [planeEmbedding_polar] at h1 h2
      apply Prod.ext
      · simpa using h2
      · simpa using h1
    refine ⟨(e v).2, ?_⟩
    rw [residualEmbedding_apply, ← hcoords]
    exact e.symm_apply_apply v

@[expose] def originalSubspaceDecomposition :
    ((Q.restrict (hyperbolicSubspace e)).prod
      (Q.restrict (residualSubspace e))).IsometryEquiv Q where
  toLinearEquiv := (hyperbolicSubspace e).prodEquivOfIsCompl
    (residualSubspace e) (hyperbolic_residual_isCompl e)
  map_app' x := by
    change Q ((x.1 : V) + x.2) = Q x.1 + Q x.2
    rw [QuadraticMap.map_add Q, hyperbolic_residual_orthogonal e x.1.2 x.2.2, add_zero]

theorem originalSubspaceDecomposition_apply
    (x : hyperbolicSubspace e × residualSubspace e) :
    originalSubspaceDecomposition e x = (x.1 : V) + x.2 :=
  Submodule.coe_prodEquivOfIsCompl' _ _ (hyperbolic_residual_isCompl e) x

theorem residualSubspace_anisotropic (hR : R.Anisotropic) :
    (Q.restrict (residualSubspace e)).Anisotropic := by
  intro x hx
  obtain ⟨y, hy⟩ := x.2
  have hy0 : R y = 0 := by
    rw [← residualEmbedding_form e, hy]
    exact hx
  apply Subtype.ext
  rw [← hy, hR y hy0, map_zero]
  rfl

end Transport

end CFSG.ComponentClassification.CatalogueBOddQuadratic
