module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairedBinaryLinearThreeTensor
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModules
public import Mathlib

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module

section Monoid

variable {k G W W' : Type*} [Field k] [Group G] [AddCommMonoid W] [Module k W] [AddCommMonoid W']
  [Module k W']

@[expose] def IsInv (ρ : Representation k G W) (U : Submodule k W) : Prop :=
  ∀ g, ∀ x ∈ U, ρ g x ∈ U

@[expose] def subrepOf (ρ : Representation k G W) (U : Submodule k W) (hU : IsInv ρ U) :
    Subrepresentation ρ :=
  ⟨U, fun g _ hx => hU g _ hx⟩

@[expose] def equivOf {ρ : Representation k G W} {σ : Representation k G W'}
    (f : W ≃ₗ[k] W') (hf : ∀ g x, f (ρ g x) = σ g (f x)) : ρ.Equiv σ :=
  { f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ hf, f with }

theorem Equiv.map_apply {ρ : Representation k G W} {σ : Representation k G W'} (e : ρ.Equiv σ)
    (g : G) (x : W) : e (ρ g x) = σ g (e x) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x

@[expose] def equivOfCompSymm {H : Type*} [Group H] {ρ : Representation k H W}
    {σ : Representation k G W'} (φ : H ≃* G)
    (e : Representation.Equiv (ρ.comp φ.symm.toMonoidHom) σ) : ρ.Equiv (σ.comp φ.toMonoidHom) :=
  equivOf e.toLinearEquiv fun h x => by
    have h1 := Equiv.map_apply e (φ h) x
    change e (ρ (φ.symm (φ h)) x) = σ (φ h) (e x) at h1
    rwa [MulEquiv.symm_apply_apply] at h1

theorem apply_mem_of_mem_span {ρ : Representation k G W} {U : Submodule k W} (hU : IsInv ρ U)
    {f : Module.End k W} (hf : f ∈ Submodule.span k (Set.range ρ)) {x : W} (hx : x ∈ U) :
    f x ∈ U := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hU g x hx
  | zero => exact U.zero_mem
  | add f f' _ _ h h' => exact U.add_mem h h'
  | smul c f _ h => exact U.smul_mem c h

theorem commute_of_mem_span {ρ : Representation k G W} {F : Module.End k W}
    (hF : ∀ g, F * ρ g = ρ g * F) {f : Module.End k W}
    (hf : f ∈ Submodule.span k (Set.range ρ)) : F * f = f * F := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hF g
  | zero => rw [mul_zero, zero_mul]
  | add f f' _ _ h h' => rw [mul_add, add_mul, h, h']
  | smul c f _ h => rw [mul_smul_comm, smul_mul_assoc, h]

@[expose] def AbsIrr (ρ : Representation k G W) : Prop :=
  Nontrivial W ∧ Submodule.span k (Set.range ρ) = ⊤

variable {H : Type*} [Group H]

@[expose] def outer (ρ : Representation k G W) (σ : Representation k H W') :
    Representation k (G × H) (TensorProduct k W W') where
  toFun p := TensorProduct.map (ρ p.1) (σ p.2)
  map_one' := by
    rw [Prod.fst_one, Prod.snd_one, map_one, map_one, TensorProduct.map_one]
  map_mul' p q := by
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, TensorProduct.map_mul]

theorem outer_apply (ρ : Representation k G W) (σ : Representation k H W') (p : G × H) :
    outer ρ σ p = TensorProduct.map (ρ p.1) (σ p.2) :=
  rfl

theorem outer_tmul (ρ : Representation k G W) (σ : Representation k H W') (p : G × H) (x : W)
    (y : W') : outer ρ σ p (x ⊗ₜ y) = ρ p.1 x ⊗ₜ σ p.2 y :=
  rfl

theorem map_mem_span_outer {ρ : Representation k G W} {σ : Representation k H W'}
    {f : Module.End k W} {f' : Module.End k W'} (hf : f ∈ Submodule.span k (Set.range ρ))
    (hf' : f' ∈ Submodule.span k (Set.range σ)) :
    TensorProduct.map f f' ∈ Submodule.span k (Set.range (outer ρ σ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    induction hf' using Submodule.span_induction with
    | mem f' hf' =>
      obtain ⟨c, rfl⟩ := hf'
      exact Submodule.subset_span ⟨(a, c), rfl⟩
    | zero =>
      rw [TensorProduct.map_zero_right]
      exact Submodule.zero_mem _
    | add f₁ f₂ _ _ h₁ h₂ =>
      rw [TensorProduct.map_add_right]
      exact Submodule.add_mem _ h₁ h₂
    | smul c f₁ _ h₁ =>
      rw [TensorProduct.map_smul_right]
      exact Submodule.smul_mem _ c h₁
  | zero =>
    rw [TensorProduct.map_zero_left]
    exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ =>
    rw [TensorProduct.map_add_left]
    exact Submodule.add_mem _ h₁ h₂
  | smul c f₁ _ h₁ =>
    rw [TensorProduct.map_smul_left]
    exact Submodule.smul_mem _ c h₁

end Monoid

section Group

variable {k G W W' : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W] [AddCommGroup W']
  [Module k W']

theorem isIrreducible_iff (ρ : Representation k G W) :
    ρ.IsIrreducible ↔ Nontrivial W ∧ ∀ U : Submodule k W, IsInv ρ U → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun U hU => ?_⟩
    · by_contra hW
      rw [not_nontrivial_iff_subsingleton] at hW
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      change (⊥ : Submodule k W) = ⊤
      exact Subsingleton.elim _ _
    · rcases h.eq_bot_or_eq_top (subrepOf ρ U hU) with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  · rintro ⟨hnt, h⟩
    obtain ⟨m, hm⟩ := exists_ne (0 : W)
    exact
      { exists_pair_ne := ⟨⊥, ⊤, CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.bot_ne_top_of_ne_zero
          ρ hm⟩
        eq_bot_or_eq_top := fun Y => by
          rcases h Y.toSubmodule (fun g x hx => Y.apply_mem_toSubmodule g hx) with h1 | h1
          · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
          · exact Or.inr (Subrepresentation.toSubmodule_injective h1) }

theorem IsIrreducible.of_equiv {ρ : Representation k G W} {σ : Representation k G W'}
    (e : ρ.Equiv σ) (hσ : σ.IsIrreducible) : ρ.IsIrreducible := by
  rw [isIrreducible_iff] at hσ ⊢
  obtain ⟨hnt, h⟩ := hσ
  refine ⟨e.toLinearEquiv.surjective.nontrivial, fun U hU => ?_⟩
  have hU' : IsInv σ (U.map e.toLinearEquiv.toLinearMap) := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hU g x hx, Equiv.map_apply e g x⟩
  rcases h _ hU' with h1 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have h2 : e.toLinearEquiv x ∈ U.map e.toLinearEquiv.toLinearMap := ⟨x, hx, rfl⟩
    rw [h1, Submodule.mem_bot] at h2
    rw [Submodule.mem_bot]
    exact e.toLinearEquiv.map_eq_zero_iff.1 h2
  · right
    rw [eq_top_iff]
    intro x _
    have hx : e.toLinearEquiv x ∈ U.map e.toLinearEquiv.toLinearMap := by
      rw [h1]
      exact Submodule.mem_top
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [e.toLinearEquiv.injective hyx] at hy

theorem isIrreducible_comp_iff {H : Type*} [Group H] (ρ : Representation k G W) (φ : H ≃* G) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom) ↔ ρ.IsIrreducible := by
  rw [isIrreducible_iff, isIrreducible_iff]
  refine and_congr Iff.rfl (forall_congr' fun U => imp_congr_left ?_)
  constructor
  · intro hU g x hx
    have h1 := hU (φ.symm g) x hx
    change ρ (φ (φ.symm g)) x ∈ U at h1
    rwa [MulEquiv.apply_symm_apply] at h1
  · intro hU h x hx
    exact hU (φ h) x hx

theorem finiteDimensional_of_isIrreducible [Finite G] {ρ : Representation k G W}
    (hρ : ρ.IsIrreducible) : FiniteDimensional k W := by
  obtain ⟨hnt, h⟩ := (isIrreducible_iff ρ).1 hρ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  set U := Submodule.span k (Set.range fun g => ρ g w) with hU
  have hinv : IsInv ρ U := fun g x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      refine Submodule.subset_span ⟨g * h, ?_⟩
      change ρ (g * h) w = ρ g (ρ h w)
      rw [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact U.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact U.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact U.smul_mem c hx
  have hfin : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range _)
  rcases h U hinv with h1 | h1
  · exfalso
    have hwU : w ∈ U := Submodule.subset_span ⟨1, by
      change ρ 1 w = w
      rw [map_one, Module.End.one_apply]⟩
    rw [h1, Submodule.mem_bot] at hwU
    exact hw hwU
  · rw [h1] at hfin
    exact LinearEquiv.finiteDimensional (LinearEquiv.ofTop ⊤ rfl)

theorem exists_minimal [FiniteDimensional k W] (ρ : Representation k G W) {U₀ : Submodule k W}
    (hU₀ : IsInv ρ U₀) (hU₀0 : U₀ ≠ ⊥) :
    ∃ U : Submodule k W, U ≤ U₀ ∧ IsInv ρ U ∧ U ≠ ⊥ ∧
      ∀ U' : Submodule k W, IsInv ρ U' → U' ≤ U → U' = ⊥ ∨ U' = U := by
  classical
  have hex : ∃ n, ∃ U : Submodule k W, U ≤ U₀ ∧ IsInv ρ U ∧ U ≠ ⊥ ∧ finrank k U = n :=
    ⟨_, U₀, le_rfl, hU₀, hU₀0, rfl⟩
  obtain ⟨U, hUU₀, hU, hU0, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hUU₀, hU, hU0, fun U' hU' hle => ?_⟩
  by_cases h0 : U' = ⊥
  · exact Or.inl h0
  · right
    have h1 := Nat.find_min' hex ⟨U', hle.trans hUU₀, hU', h0, rfl⟩
    rw [← hUn] at h1
    exact Submodule.eq_of_le_of_finrank_le hle h1

theorem isIrreducible_subrepOf {ρ : Representation k G W} {U : Submodule k W} (hU : IsInv ρ U)
    (hU0 : U ≠ ⊥) (hmin : ∀ U' : Submodule k W, IsInv ρ U' → U' ≤ U → U' = ⊥ ∨ U' = U) :
    (subrepOf ρ U hU).toRepresentation.IsIrreducible := by
  rw [isIrreducible_iff]
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hU0, fun Y hY => ?_⟩
  have hYinv : IsInv ρ (Y.map U.subtype) := by
    rintro g _ ⟨y, hy, rfl⟩
    exact ⟨_, hY g y hy, rfl⟩
  rcases hmin _ hYinv (Submodule.map_subtype_le U Y) with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : U.subtype y ∈ Y.map U.subtype := ⟨y, hy, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Subtype.ext h1
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : (y : W) ∈ Y.map U.subtype := by rw [h]; exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    rwa [show y' = y from Subtype.ext hyy'] at hy'

end Group

section Absolute

variable {k G W W' : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W] [AddCommGroup W']
  [Module k W']

theorem AbsIrr.isIrreducible {ρ : Representation k G W} (h : AbsIrr ρ) : ρ.IsIrreducible := by
  rw [isIrreducible_iff]
  refine ⟨h.1, fun U hU => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hu0
  rw [eq_top_iff]
  intro w _
  have h1 : (φ.smulRight w) u ∈ U := apply_mem_of_mem_span hU (h.2 ▸ Submodule.mem_top) hu
  rwa [LinearMap.smulRight_apply, hφ, one_smul] at h1

theorem AbsIrr.eq_smul {ρ : Representation k G W} (h : AbsIrr ρ) (F : Module.End k W)
    (hF : ∀ g, F * ρ g = ρ g * F) : ∃ c : k, F = c • 1 := by
  have hc : F ∈ Set.center (Module.End k W) := by
    rw [Semigroup.mem_center_iff]
    intro f
    exact (commute_of_mem_span hF (h.2 ▸ Submodule.mem_top : f ∈ _)).symm
  obtain ⟨α, hα0, hα⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, hα.trans (LinearMap.ext fun x => rfl)⟩

theorem AbsIrr.of_equiv {ρ : Representation k G W} {σ : Representation k G W'}
    (e : ρ.Equiv σ) (h : AbsIrr σ) : AbsIrr ρ := by
  have := h.1
  refine ⟨e.toLinearEquiv.surjective.nontrivial, ?_⟩
  set c := e.toLinearEquiv.symm.conj with hc
  have himage : c '' Set.range σ = Set.range ρ := by
    ext f
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g, LinearMap.ext fun x => ?_⟩
      rw [hc, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
      apply e.toLinearEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Equiv.map_apply e g x
    · rintro ⟨g, rfl⟩
      refine ⟨σ g, ⟨g, rfl⟩, LinearMap.ext fun x => ?_⟩
      rw [hc, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
      apply e.toLinearEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (Equiv.map_apply e g x).symm
  rw [← himage, show (⇑c '' Set.range σ) = (c.toLinearMap) '' Set.range σ from rfl,
    ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact c.surjective

theorem span_range_eq_top [FiniteDimensional k W] (ρ : Representation k G W)
    (hρ : ρ.IsIrreducible)
    (hend : ∀ f : W →ₗ[k] W, (∀ g x, f (ρ g x) = ρ g (f x)) → ∃ c : k, f = c • LinearMap.id) :
    Submodule.span k (Set.range ρ) = ⊤ := by
  classical
  have : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  set ι := ρ.asModuleEquiv with hι
  have hcm : ∀ (c : k) (m : ρ.asModule),
      c • m = (algebraMap k (MonoidAlgebra k G) c) • m := fun c m => by
    apply ι.injective
    rw [map_smul, hι, Representation.asModuleEquiv_map_smul, AlgHom.commutes,
      Module.algebraMap_end_apply]
  have hEnd : ∀ e : Module.End (MonoidAlgebra k G) ρ.asModule, ∃ c : k, ∀ m, e m = c • m := by
    intro e
    let f : W →ₗ[k] W :=
      { toFun := fun x => ι (e (ι.symm x))
        map_add' := fun x y => by rw [map_add, map_add, map_add]
        map_smul' := fun c x => by
          change ι (e (ι.symm (c • x))) = c • ι (e (ι.symm x))
          rw [map_smul, hcm, e.map_smul, ← hcm, map_smul] }
    have hf : ∀ g x, f (ρ g x) = ρ g (f x) := fun g x => by
      change ι (e (ι.symm (ρ g x))) = ρ g (ι (e (ι.symm x)))
      rw [hι, ρ.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_of]
    obtain ⟨c, hc⟩ := hend f hf
    refine ⟨c, fun m => ?_⟩
    have h1 := LinearMap.congr_fun hc (ι m)
    change ι (e (ι.symm (ι m))) = c • ι m at h1
    rw [LinearEquiv.symm_apply_apply] at h1
    apply ι.injective
    rw [h1, map_smul]
  rw [eq_top_iff]
  intro φ _
  let φM : Module.End (Module.End (MonoidAlgebra k G) ρ.asModule) ρ.asModule :=
    { toFun := fun m => ι.symm (φ (ι m))
      map_add' := fun m m' => by rw [map_add, map_add, map_add]
      map_smul' := fun e m => by
        change ι.symm (φ (ι (e m))) = e (ι.symm (φ (ι m)))
        obtain ⟨c, hc⟩ := hEnd e
        rw [hc, hc, map_smul, map_smul, map_smul] }
  obtain ⟨b⟩ := Module.Free.exists_basis (R := k) (M := W)
  have hfin : Finite b.1 := Module.Finite.finite_basis b.2
  have : Fintype b.1 := Fintype.ofFinite _
  obtain ⟨r, hr⟩ := jacobson_density φM (Finset.univ.image fun i => ι.symm (b.2 i))
  have hφ : φ = ρ.asAlgebraHom r := b.2.ext fun i => by
    have h1 := hr (ι.symm (b.2 i)) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    change ι.symm (φ (ι (ι.symm (b.2 i)))) = r • ι.symm (b.2 i) at h1
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 := congrArg ι h1
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] at h2
    exact h2
  rw [hφ, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem AbsIrr.of_isIrreducible [FiniteDimensional k W] {ρ : Representation k G W}
    (hρ : ρ.IsIrreducible)
    (hend : ∀ f : W →ₗ[k] W, (∀ g x, f (ρ g x) = ρ g (f x)) → ∃ c : k, f = c • LinearMap.id) :
    AbsIrr ρ :=
  ⟨((isIrreducible_iff ρ).1 hρ).1, span_range_eq_top ρ hρ hend⟩

variable {H : Type*} [Group H]

theorem AbsIrr.outer [FiniteDimensional k W] [FiniteDimensional k W'] {ρ : Representation k G W}
    {σ : Representation k H W'} (hρ : AbsIrr ρ) (hσ : AbsIrr σ) : AbsIrr (outer ρ σ) := by
  have := hρ.1
  have := hσ.1
  refine ⟨Module.nontrivial_of_finrank_pos (R := k) (by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos (Module.finrank_pos (R := k) (M := W))
      (Module.finrank_pos (R := k) (M := W'))), ?_⟩
  rw [eq_top_iff]
  rintro F -
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv k W W' W W').surjective F
  have ht : t ∈ (⊤ : Submodule k (TensorProduct k (Module.End k W) (Module.End k W'))) :=
    Submodule.mem_top
  rw [← TensorProduct.span_tmul_eq_top] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨f, f', rfl⟩ := ht
    rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
    exact map_mem_span_outer (hρ.2 ▸ Submodule.mem_top) (hσ.2 ▸ Submodule.mem_top)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add t t' _ _ h h' =>
    rw [map_add]
    exact Submodule.add_mem _ h h'
  | smul c t _ h =>
    rw [map_smul]
    exact Submodule.smul_mem _ c h

end Absolute

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
