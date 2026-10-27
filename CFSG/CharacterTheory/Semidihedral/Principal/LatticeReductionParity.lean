module

public import CFSG.CharacterTheory.Semidihedral.Principal.SelfDualCharacteristicTwoParity
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Tactic.ENatToNat

public section

open scoped Classical TensorProduct Pointwise

namespace CFSG.Semidihedral.Principal

open Representation

section Definitions

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [Group G]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

@[expose] noncomputable def latticeReduction (π : R) (ρ : Representation K G V) (L : Submodule R V)
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) :
    Representation (R ⧸ Ideal.span {π}) G (L ⧸ (Ideal.span {π} • ⊤ : Submodule R L)) where
  toFun g := (((ρ g).restrictScalars R).restrict (hL g)).reduceModIdeal (Ideal.span {π})
  map_one' := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.reduceModIdeal_apply]
      congr 1
      ext
      simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      simp only [Module.End.mul_apply, LinearMap.reduceModIdeal_apply]
      congr 1
      ext
      simp only [map_mul]
      rfl

@[simp]
theorem latticeReduction_apply_mk (π : R) (ρ : Representation K G V) (L : Submodule R V)
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (g : G) (x : L) :
    latticeReduction π ρ L hL g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨ρ g x, hL g x x.2⟩ :=
  rfl

end Definitions

section BaseChange

variable {k G W : Type*} [CommRing k] [Monoid G] [AddCommGroup W] [Module k W]

@[expose] noncomputable def baseChangeRepresentation (K' : Type*) [CommRing K'] [Algebra k K']
    (σ : Representation k G W) : Representation K' G (K' ⊗[k] W) where
  toFun g := (σ g).baseChange K'
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_id
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.baseChange_mul _ _

@[simp]
theorem baseChangeRepresentation_tmul (K' : Type*) [CommRing K'] [Algebra k K']
    (σ : Representation k G W) (g : G) (a : K') (w : W) :
    baseChangeRepresentation K' σ g (a ⊗ₜ w) = a ⊗ₜ σ g w :=
  rfl

end BaseChange

section ExactPair

theorem compositionMultiplicity_eq_of_exact_pair {A X Y : Type*} [Ring A] [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] [IsNoetherian A X] [IsArtinian A X]
    [IsNoetherian A Y] [IsArtinian A Y] (F : Y →ₗ[A] X) (Φ : X →ₗ[A] Y)
    (h₁ : Function.Exact Φ F) (h₂ : Function.Exact F Φ) (S : Type*) [AddCommGroup S]
    [Module A S] : compositionMultiplicity A X S = compositionMultiplicity A Y S := by
  have hk1 : LinearMap.ker F = LinearMap.range Φ := LinearMap.exact_iff.mp h₁
  have hk2 : LinearMap.ker Φ = LinearMap.range F := LinearMap.exact_iff.mp h₂
  calc compositionMultiplicity A X S
      = compositionMultiplicity A (LinearMap.ker Φ) S +
          compositionMultiplicity A (X ⧸ LinearMap.ker Φ) S :=
        compositionMultiplicity_eq_submodule_add_quotient _ S
    _ = compositionMultiplicity A (LinearMap.range F) S +
          compositionMultiplicity A (LinearMap.range Φ) S := by
        rw [compositionMultiplicity_congr_left (LinearEquiv.ofEq _ _ hk2) S,
          compositionMultiplicity_congr_left Φ.quotKerEquivRange S]
    _ = compositionMultiplicity A (LinearMap.ker F) S +
          compositionMultiplicity A (Y ⧸ LinearMap.ker F) S := by
        rw [compositionMultiplicity_congr_left (LinearEquiv.ofEq _ _ hk1) S,
          compositionMultiplicity_congr_left F.quotKerEquivRange S, add_comm]
    _ = compositionMultiplicity A Y S :=
        (compositionMultiplicity_eq_submodule_add_quotient _ S).symm

variable {k G X Y W : Type*} [Field k] [Monoid G] [AddCommGroup X] [Module k X] [AddCommGroup Y]
  [Module k Y] [AddCommGroup W]

theorem repMultiplicity_eq_of_exact_pair [Module k W] [FiniteDimensional k X]
    [FiniteDimensional k Y] {ρX : Representation k G X} {ρY : Representation k G Y}
    (F : ρY.IntertwiningMap ρX) (Φ : ρX.IntertwiningMap ρY) (h₁ : Function.Exact Φ F)
    (h₂ : Function.Exact F Φ) (σ : Representation k G W) :
    repMultiplicity ρX σ = repMultiplicity ρY σ := by
  have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρX.asModule)
  have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρX.asModule)
  have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρY.asModule)
  have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρY.asModule)
  exact compositionMultiplicity_eq_of_exact_pair
    (IntertwiningMap.equivLinearMapAsModule ρY ρX F)
    (IntertwiningMap.equivLinearMapAsModule ρX ρY Φ) h₁ h₂ σ.asModule

noncomputable def baseChangeIntertwiningMap (K' : Type*) [Field K'] [Algebra k K']
    {ρX : Representation k G X} {ρY : Representation k G Y} (F : ρY.IntertwiningMap ρX) :
    (baseChangeRepresentation K' ρY).IntertwiningMap (baseChangeRepresentation K' ρX) where
  toLinearMap := F.toLinearMap.baseChange K'
  isIntertwining' g := by
    change F.toLinearMap.baseChange K' ∘ₗ (ρY g).baseChange K' =
      (ρX g).baseChange K' ∘ₗ F.toLinearMap.baseChange K'
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact F.isIntertwining' g

theorem baseChangeIntertwiningMap_exact (K' : Type*) [Field K'] [Algebra k K']
    {ρX : Representation k G X} {ρY : Representation k G Y} (F : ρY.IntertwiningMap ρX)
    (Φ : ρX.IntertwiningMap ρY) (h : Function.Exact Φ F) :
    Function.Exact (baseChangeIntertwiningMap K' Φ) (baseChangeIntertwiningMap K' F) := by
  change Function.Exact (Φ.toLinearMap.baseChange K') (F.toLinearMap.baseChange K')
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_exact K' h

theorem repMultiplicity_baseChange_eq_of_exact_pair [FiniteDimensional k X]
    [FiniteDimensional k Y] {ρX : Representation k G X} {ρY : Representation k G Y}
    (F : ρY.IntertwiningMap ρX) (Φ : ρX.IntertwiningMap ρY) (h₁ : Function.Exact Φ F)
    (h₂ : Function.Exact F Φ) (K' : Type*) [Field K'] [Algebra k K'] [Module K' W]
    (σ : Representation K' G W) :
    repMultiplicity (baseChangeRepresentation K' ρX) σ =
      repMultiplicity (baseChangeRepresentation K' ρY) σ :=
  repMultiplicity_eq_of_exact_pair (baseChangeIntertwiningMap K' F)
    (baseChangeIntertwiningMap K' Φ) (baseChangeIntertwiningMap_exact K' F Φ h₁)
    (baseChangeIntertwiningMap_exact K' Φ F h₂) σ

end ExactPair

section ReductionStep

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [Group G]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

omit [Field K] [Algebra R K] [Module K V] [IsScalarTower R K V] in
theorem mem_ideal_span_smul_top_iff (π : R) {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    x ∈ (Ideal.span {π} • ⊤ : Submodule R M) ↔ ∃ m : M, π • m = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

@[expose] def piMap (π : R) {M M' : Submodule R V} (hπM : ∀ x ∈ M, π • x ∈ M') :
    M →ₗ[R] M' where
  toFun x := ⟨π • (x : V), hπM x x.2⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' r x := by ext; simp [smul_comm π r]

variable (π : R) (ρ : Representation K G V)

noncomputable def reductionInclusion {M M' : Submodule R V} (hle : M' ≤ M)
    (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M) (hM' : ∀ g, ∀ x ∈ M', ρ g x ∈ M') :
    (latticeReduction π ρ M' hM').IntertwiningMap (latticeReduction π ρ M hM) where
  toLinearMap := (Submodule.inclusion hle).reduceModIdeal (Ideal.span {π})
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

noncomputable def reductionPiMap {M M' : Submodule R V} (hπM : ∀ x ∈ M, π • x ∈ M')
    (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M) (hM' : ∀ g, ∀ x ∈ M', ρ g x ∈ M') :
    (latticeReduction π ρ M hM).IntertwiningMap (latticeReduction π ρ M' hM') where
  toLinearMap := (piMap π hπM).reduceModIdeal (Ideal.span {π})
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      ext
      change π • ρ g (x : V) = ρ g (π • (x : V))
      rw [LinearMap.map_smul_of_tower]

theorem reduction_exact_pi_inclusion {M M' : Submodule R V} (hle : M' ≤ M)
    (hπM : ∀ x ∈ M, π • x ∈ M') (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M)
    (hM' : ∀ g, ∀ x ∈ M', ρ g x ∈ M') :
    Function.Exact (reductionPiMap π ρ hπM hM hM') (reductionInclusion π ρ hle hM hM') := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x' =>
    change (Submodule.Quotient.mk (Submodule.inclusion hle x') : M ⧸ _) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_ideal_span_smul_top_iff]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨Submodule.Quotient.mk m, ?_⟩
      change Submodule.Quotient.mk (piMap π hπM m) = Submodule.Quotient.mk x'
      congr 1
      ext
      change π • (m : V) = x'
      have := congrArg Subtype.val hm
      simpa using this
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with
      | H m =>
        change Submodule.Quotient.mk (piMap π hπM m) = Submodule.Quotient.mk x' at hz
        rw [Submodule.Quotient.eq, mem_ideal_span_smul_top_iff] at hz
        obtain ⟨m'', hm''⟩ := hz
        refine ⟨m - Submodule.inclusion hle m'', ?_⟩
        ext
        have := congrArg Subtype.val hm''
        simp only [Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_inclusion] at this ⊢
        change π • ((m : V) - (m'' : V)) = (x' : V)
        rw [smul_sub, this]
        change π • (m : V) - (π • (m : V) - (x' : V)) = (x' : V)
        abel

theorem reduction_exact_inclusion_pi [IsFractionRing R K] {π : R} (hπ : π ≠ 0)
    {M M' : Submodule R V} (hle : M' ≤ M) (hπM : ∀ x ∈ M, π • x ∈ M')
    (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M) (hM' : ∀ g, ∀ x ∈ M', ρ g x ∈ M') :
    Function.Exact (reductionInclusion π ρ hle hM hM') (reductionPiMap π ρ hπM hM hM') := by
  have htf : ∀ v w : V, π • v = π • w → v = w := by
    intro v w h
    have hπK : algebraMap R K π ≠ 0 :=
      fun h0 => hπ (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
    rw [← algebraMap_smul K π v, ← algebraMap_smul K π w] at h
    exact smul_right_injective V hπK h
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H m =>
    change (Submodule.Quotient.mk (piMap π hπM m) : M' ⧸ _) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_ideal_span_smul_top_iff]
    constructor
    · rintro ⟨m', hm'⟩
      have hmm' : (m' : V) = m := htf _ _ (congrArg Subtype.val hm')
      refine ⟨Submodule.Quotient.mk m', ?_⟩
      change Submodule.Quotient.mk (Submodule.inclusion hle m') = Submodule.Quotient.mk m
      congr 1
      ext
      exact hmm'
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with
      | H x' =>
        change Submodule.Quotient.mk (Submodule.inclusion hle x') = Submodule.Quotient.mk m at hy
        rw [Submodule.Quotient.eq, mem_ideal_span_smul_top_iff] at hy
        obtain ⟨m₁, hm₁⟩ := hy
        have hm₁V : π • (m₁ : V) = (x' : V) - m := congrArg Subtype.val hm₁
        refine ⟨x' - ⟨π • (m₁ : V), hπM _ m₁.2⟩, ?_⟩
        ext
        change π • ((x' : V) - π • (m₁ : V)) = π • (m : V)
        rw [hm₁V]
        congr 1
        abel

end ReductionStep

section Chain

variable {R K G V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Group G] [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
noncomputable def baseChangeSelfEquiv {k W : Type*} [CommRing k] [AddCommGroup W] [Module k W]
    (σ : Representation k G W) : (baseChangeRepresentation k σ).Equiv σ :=
  Representation.Equiv.mk (TensorProduct.lid k W) fun g => by
    apply TensorProduct.ext'
    intro a w
    simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Group G] in
theorem finite_of_le [IsNoetherianRing R] {A B : Submodule R V} (h : A ≤ B)
    [Module.Finite R B] : Module.Finite R A :=
  Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem repMultiplicity_baseChange_reduction_congr {π : R} (ρ : Representation K G V)
    {L L' : Submodule R V} (h : L = L') (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L)
    (hL' : ∀ g, ∀ x ∈ L', ρ g x ∈ L') (K' : Type*) [CommRing K']
    [Algebra (R ⧸ Ideal.span {π}) K'] {W : Type*} [AddCommGroup W] [Module K' W]
    (σ : Representation K' G W) :
    repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L hL)) σ =
      repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L' hL')) σ := by
  subst h
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem invariant_pow_smul {ρ : Representation K G V} {L : Submodule R V}
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (r : R) : ∀ g, ∀ x ∈ r • L, ρ g x ∈ r • L := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (hL g y hy)

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
  [IsScalarTower R K V] in
theorem invariant_sup_of {ρ : Representation K G V} {L N : Submodule R V}
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (hN : ∀ g, ∀ x ∈ N, ρ g x ∈ N) :
    ∀ g, ∀ x ∈ N ⊔ L, ρ g x ∈ N ⊔ L := by
  intro g x hx
  obtain ⟨n, hn, l, hl, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (hN g n hn) (hL g l hl)

theorem repMultiplicity_baseChange_reduction_step {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) {M M' : Submodule R V} (hle : M' ≤ M)
    (hπM : ∀ x ∈ M, π • x ∈ M') (hM : ∀ g, ∀ x ∈ M, ρ g x ∈ M)
    (hM' : ∀ g, ∀ x ∈ M', ρ g x ∈ M') [Module.Finite R M] [Module.Finite R M']
    (K' : Type*) [Field K'] [Algebra (R ⧸ Ideal.span {π}) K'] {W : Type*} [AddCommGroup W]
    [Module K' W] (σ : Representation K' G W) :
    repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ M hM)) σ =
      repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ M' hM')) σ := by
  have : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  exact repMultiplicity_baseChange_eq_of_exact_pair (reductionInclusion π ρ hle hM hM')
    (reductionPiMap π ρ hπM hM hM') (reduction_exact_pi_inclusion π ρ hle hπM hM hM')
    (reduction_exact_inclusion_pi ρ hπ.ne_zero hle hπM hM hM') K' σ

theorem repMultiplicity_baseChange_reduction_of_le {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) {L N : Submodule R V} (hNL : N ≤ L) {b : ℕ}
    (hb : π ^ b • L ≤ N) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (hN : ∀ g, ∀ x ∈ N, ρ g x ∈ N)
    [Module.Finite R L] (K' : Type*) [Field K'] [Algebra (R ⧸ Ideal.span {π}) K']
    {W : Type*} [AddCommGroup W] [Module K' W] (σ : Representation K' G W) :
    repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L hL)) σ =
      repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ N hN)) σ := by
  have hchain : ∀ j ≤ b,
      repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L hL)) σ =
        repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ (N ⊔ π ^ j • L)
          (invariant_sup_of (invariant_pow_smul hL _) hN))) σ := by
    intro j hj
    induction j with
    | zero =>
      have hsup : N ⊔ π ^ 0 • L = L := by rw [pow_zero, one_smul, sup_eq_right.mpr hNL]
      exact repMultiplicity_baseChange_reduction_congr ρ hsup.symm _ _ K' σ
    | succ j ih =>
      rw [ih (Nat.le_of_succ_le hj)]
      have hle : N ⊔ π ^ (j + 1) • L ≤ N ⊔ π ^ j • L := by
        refine sup_le_sup_left ?_ _
        intro x hx
        obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        rw [pow_succ, mul_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ (L.smul_mem _ hy)
      have hπM : ∀ x ∈ N ⊔ π ^ j • L, π • x ∈ N ⊔ π ^ (j + 1) • L := by
        intro x hx
        obtain ⟨n, hn, l, hl, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hl
        rw [smul_add]
        refine Submodule.add_mem_sup (N.smul_mem _ hn) ?_
        rw [smul_smul, ← pow_succ']
        exact Submodule.smul_mem_pointwise_smul _ _ _ hy
      have hfin₁ : Module.Finite R ↥(N ⊔ π ^ j • L) :=
        finite_of_le (sup_le hNL (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
          exact L.smul_mem _ hy))
      have hfin₂ : Module.Finite R ↥(N ⊔ π ^ (j + 1) • L) := finite_of_le (hle.trans
        (sup_le hNL (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
          exact L.smul_mem _ hy)))
      exact repMultiplicity_baseChange_reduction_step hπ ρ hle hπM _ _ K' σ
  rw [hchain b le_rfl]
  exact repMultiplicity_baseChange_reduction_congr ρ (sup_eq_left.mpr hb) _ _ K' σ

end Chain

section Commensurable

variable {R K G V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Group G] [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]

omit [Group G] in
theorem exists_pow_smul_le {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hL : Submodule.span K (L : Set V) = ⊤) (N : Submodule R V) (hN : N.FG) :
    ∃ a : ℕ, π ^ a • N ≤ L := by
  let S : Submodule K V :=
    { carrier := {v | ∃ a : ℕ, π ^ a • v ∈ L}
      add_mem' := by
        rintro v w ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        rw [smul_add, pow_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]
          exact L.smul_mem _ ha
        · rw [mul_smul]
          exact L.smul_mem _ hb
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c v ⟨a, ha⟩
        obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
        have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hπ
        refine ⟨m + a, ?_⟩
        have hsK : algebraMap R K s ≠ 0 :=
          fun h0 => hs (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
        have hπK : algebraMap R K π ≠ 0 :=
          fun h0 => hπ.ne_zero (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
        have huK : algebraMap R K (u : R) * algebraMap R K ((u⁻¹ : Rˣ) : R) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have key : π ^ (m + a) • (IsLocalization.mk' K r s • v) =
            (((u⁻¹ : Rˣ) : R) * r) • (π ^ a • v) := by
          rw [← algebraMap_smul K (π ^ (m + a)), smul_smul,
            ← algebraMap_smul K (((u⁻¹ : Rˣ) : R) * r), ← algebraMap_smul K (π ^ a) v, smul_smul]
          congr 1
          rw [IsFractionRing.mk'_eq_div, hu]
          simp only [map_mul, map_pow]
          rw [hu, map_mul, map_pow] at hsK
          field_simp
          linear_combination -(algebraMap R K r * algebraMap R K π ^ a *
            algebraMap R K π ^ m) * huK
        rw [key]
        exact L.smul_mem _ ha }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hL, Submodule.span_le]
    intro v hv
    exact ⟨0, by simpa using hv⟩
  obtain ⟨t, rfl⟩ := hN
  have ht : ∀ v ∈ t, ∃ a : ℕ, π ^ a • v ∈ L := fun v _ => by
    have : v ∈ S := hS ▸ Submodule.mem_top
    exact this
  choose f hf using ht
  refine ⟨∑ v ∈ t.attach, f v.1 v.2, ?_⟩
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  have hle : f v hv ≤ ∑ w ∈ t.attach, f w.1 w.2 :=
    Finset.single_le_sum (f := fun w : t => f w.1 w.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_attach t ⟨v, hv⟩)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  change π ^ (∑ w ∈ t.attach, f w.1 w.2) • v ∈ L
  rw [hc, pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ (hf v hv)

omit [IsDomain R] [IsDiscreteValuationRing R] [Group G] in
theorem span_pow_smul_eq_top {π : R} (hπ : π ≠ 0) {L : Submodule R V}
    (hL : Submodule.span K (L : Set V) = ⊤) (a : ℕ) :
    Submodule.span K ((π ^ a • L : Submodule R V) : Set V) = ⊤ := by
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have hπK : algebraMap R K π ≠ 0 :=
    fun h0 => hπ (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  have hmem : π ^ a • x ∈ ((π ^ a • L : Submodule R V) : Set V) :=
    Submodule.smul_mem_pointwise_smul _ _ _ hx
  have : x = (algebraMap R K π ^ a)⁻¹ • (π ^ a • x) := by
    rw [← algebraMap_smul K (π ^ a) x, smul_smul, map_pow, inv_mul_cancel₀ (pow_ne_zero _ hπK),
      one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem repMultiplicity_baseChange_latticeReduction_eq {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) {L₁ L₂ : Submodule R V} (hL₁ : ∀ g, ∀ x ∈ L₁, ρ g x ∈ L₁)
    (hL₂ : ∀ g, ∀ x ∈ L₂, ρ g x ∈ L₂) [Module.Finite R L₁] [Module.Finite R L₂]
    (hsp₁ : Submodule.span K (L₁ : Set V) = ⊤) (hsp₂ : Submodule.span K (L₂ : Set V) = ⊤)
    (K' : Type*) [Field K'] [Algebra (R ⧸ Ideal.span {π}) K'] {W : Type*} [AddCommGroup W]
    [Module K' W] (σ : Representation K' G W) :
    repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L₁ hL₁)) σ =
      repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L₂ hL₂)) σ := by
  obtain ⟨a, ha⟩ := exists_pow_smul_le hπ hsp₁ L₂ (Module.Finite.iff_fg.mp inferInstance)
  obtain ⟨b, hb⟩ := exists_pow_smul_le hπ (span_pow_smul_eq_top hπ.ne_zero hsp₂ a) L₁
    (Module.Finite.iff_fg.mp inferInstance)
  have hN := invariant_pow_smul hL₂ (π ^ a)
  have hNL₂ : π ^ a • L₂ ≤ L₂ := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact L₂.smul_mem _ hy
  rw [repMultiplicity_baseChange_reduction_of_le hπ ρ ha hb hL₁ hN K' σ,
    repMultiplicity_baseChange_reduction_of_le hπ ρ hNL₂ (le_refl _) hL₂ hN K' σ]

theorem repMultiplicity_latticeReduction_eq {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) {L₁ L₂ : Submodule R V} (hL₁ : ∀ g, ∀ x ∈ L₁, ρ g x ∈ L₁)
    (hL₂ : ∀ g, ∀ x ∈ L₂, ρ g x ∈ L₂) [Module.Finite R L₁] [Module.Finite R L₂]
    (hsp₁ : Submodule.span K (L₁ : Set V) = ⊤) (hsp₂ : Submodule.span K (L₂ : Set V) = ⊤)
    {W : Type*} [AddCommGroup W] [Module (R ⧸ Ideal.span {π}) W]
    (σ : Representation (R ⧸ Ideal.span {π}) G W) :
    repMultiplicity (latticeReduction π ρ L₁ hL₁) σ =
      repMultiplicity (latticeReduction π ρ L₂ hL₂) σ := by
  have : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  rw [← repMultiplicity_congr_left (baseChangeSelfEquiv (latticeReduction π ρ L₁ hL₁)) σ,
    ← repMultiplicity_congr_left (baseChangeSelfEquiv (latticeReduction π ρ L₂ hL₂)) σ]
  exact repMultiplicity_baseChange_latticeReduction_eq hπ ρ hL₁ hL₂ hsp₁ hsp₂ _ σ

end Commensurable

section DualLattice

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

noncomputable def latticeBasis {L : Submodule R V} [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) {ι : Type*} (e : Module.Basis ι R L) :
    Module.Basis ι K V :=
  have : Submodule.IsLattice K L := ⟨Module.Finite.iff_fg.mp inferInstance, hsp⟩
  e.extendOfIsLattice K

theorem latticeBasis_apply {L : Submodule R V} [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) {ι : Type*} (e : Module.Basis ι R L) (i : ι) :
    latticeBasis hsp e i = (e i : V) := by
  have : Submodule.IsLattice K L := ⟨Module.Finite.iff_fg.mp inferInstance, hsp⟩
  exact e.extendOfIsLattice_apply K i

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairingDualBasis (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V) :
    Module.Basis ι K V :=
  b.dualBasis.map φ.symm

theorem pairingDualBasis_pairing (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V)
    (i j : ι) : φ (pairingDualBasis φ b i) (b j) = if j = i then 1 else 0 := by
  rw [pairingDualBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]

noncomputable abbrev dualLattice (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V) :
    Submodule R V :=
  Submodule.span R (Set.range (pairingDualBasis φ b))

theorem dualLattice_linearIndependent (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V) :
    LinearIndependent R (pairingDualBasis φ b) :=
  (LinearIndependent.iff_fractionRing R K).mpr (pairingDualBasis φ b).linearIndependent

omit [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
theorem dualLattice_span_eq_top (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V) :
    Submodule.span K ((dualLattice (R := R) φ b : Submodule R V) : Set V) = ⊤ := by
  rw [eq_top_iff, ← (pairingDualBasis φ b).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩)

omit [IsFractionRing R K] in
theorem mem_dualLattice_iff (φ : V ≃ₗ[K] Module.Dual K V) (b : Module.Basis ι K V) (v : V) :
    v ∈ dualLattice (R := R) φ b ↔ ∀ j, φ v (b j) ∈ (algebraMap R K).range := by
  constructor
  · intro hv j
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [pairingDualBasis_pairing]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add, ha, hc, map_add, LinearMap.add_apply]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, ← algebraMap_smul K r x, map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro hv
    choose c hc using hv
    have hexp : v = ∑ j, algebraMap R K (c j) • pairingDualBasis φ b j := by
      apply φ.injective
      rw [map_sum]
      apply b.ext
      intro i
      rw [LinearMap.sum_apply, Finset.sum_eq_single i]
      · rw [map_smul, LinearMap.smul_apply, pairingDualBasis_pairing, ite_eq_left rfl, hc,
          smul_eq_mul, mul_one]
      · intro j _ hji
        rw [map_smul, LinearMap.smul_apply, pairingDualBasis_pairing, ite_eq_right (Ne.symm hji),
          smul_zero]
      · simp
    rw [hexp]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLattice

section ReductionBasis

variable {R : Type*} [CommRing R] (π : R) {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*}

noncomputable def reductionBasis (b : Module.Basis ι R M) :
    Module.Basis ι (R ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule R M)) :=
  (Algebra.TensorProduct.basis (R ⧸ Ideal.span {π}) b).map
    ((TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {π})).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)

theorem reductionBasis_apply (b : Module.Basis ι R M) (i : ι) :
    reductionBasis π b i = Submodule.Quotient.mk (b i) := by
  rw [reductionBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    LinearEquiv.extendScalarsOfSurjective_apply, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

theorem reductionBasis_repr_mk (b : Module.Basis ι R M) (x : M) (i : ι) :
    (reductionBasis π b).repr (Submodule.Quotient.mk x) i =
      Ideal.Quotient.mk (Ideal.span {π}) (b.repr x i) := by
  rw [reductionBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.extendScalarsOfSurjective_symm, LinearEquiv.extendScalarsOfSurjective_apply,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk, Algebra.TensorProduct.basis_repr_tmul,
    one_smul, Finsupp.mapRange_apply]
  rfl

end ReductionBasis

section SelfDuality

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Group G]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coe_eq_sum_latticeBasis {L : Submodule R V} [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) (e : Module.Basis ι R L) (x : L) :
    (x : V) = ∑ j, algebraMap R K (e.repr x j) • latticeBasis hsp e j := by
  conv_lhs => rw [← e.sum_repr x]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, algebraMap_smul, latticeBasis_apply]

omit [DecidableEq ι] in
theorem integral_of_mem_lattice (φ : V ≃ₗ[K] Module.Dual K V) {L : Submodule R V}
    [Module.Finite R L] (hsp : Submodule.span K (L : Set V) = ⊤) (e : Module.Basis ι R L)
    {v : V} (hv : ∀ i, φ v (latticeBasis hsp e i) ∈ (algebraMap R K).range) {x : V}
    (hx : x ∈ L) : φ v x ∈ (algebraMap R K).range := by
  have h := coe_eq_sum_latticeBasis hsp e ⟨x, hx⟩
  simp only at h
  rw [h, map_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  exact Subring.mul_mem _ ⟨_, rfl⟩ (hv j)

theorem dualLattice_invariant (ρ : Representation K G V) (φ : V ≃ₗ[K] Module.Dual K V)
    (hφ : ∀ g v, φ (ρ g v) = ρ.dual g (φ v)) {L : Submodule R V}
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) [Module.Finite R L] (hsp : Submodule.span K (L : Set V) = ⊤)
    (e : Module.Basis ι R L) :
    ∀ g, ∀ v ∈ dualLattice (R := R) φ (latticeBasis hsp e),
      ρ g v ∈ dualLattice (R := R) φ (latticeBasis hsp e) := by
  intro g v hv
  rw [mem_dualLattice_iff] at hv ⊢
  intro j
  rw [hφ, dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  refine integral_of_mem_lattice φ hsp e hv (hL g⁻¹ _ ?_)
  rw [latticeBasis_apply]
  exact (e j).2

noncomputable def latticePairing {L L' : Submodule R V} (fL : Module.Basis ι R L')
    (e : Module.Basis ι R L) (v : L') (x : L) : R :=
  ∑ i, fL.repr v i * e.repr x i

theorem algebraMap_latticePairing (φ : V ≃ₗ[K] Module.Dual K V) {L : Submodule R V}
    [Module.Finite R L] (hsp : Submodule.span K (L : Set V) = ⊤) (e : Module.Basis ι R L)
    (v : dualLattice (R := R) φ (latticeBasis hsp e)) (x : L) :
    algebraMap R K (latticePairing (Module.Basis.span (dualLattice_linearIndependent φ
      (latticeBasis hsp e))) e v x) = φ v x := by
  set fL := Module.Basis.span (R := R) (dualLattice_linearIndependent φ (latticeBasis hsp e))
  have hv : (v : V) =
      ∑ i, algebraMap R K (fL.repr v i) • pairingDualBasis φ (latticeBasis hsp e) i := by
    conv_lhs => rw [← fL.sum_repr v]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, algebraMap_smul, Module.Basis.span_apply]
  rw [hv, map_sum, LinearMap.sum_apply, latticePairing, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, coe_eq_sum_latticeBasis hsp e x, map_sum,
    Finset.sum_eq_single i]
  · rw [map_smul, pairingDualBasis_pairing, ite_eq_left rfl, smul_eq_mul, mul_one, map_mul]
  · intro j _ hji
    rw [map_smul, pairingDualBasis_pairing, ite_eq_right hji, smul_zero]
  · simp

end SelfDuality

section Psi

theorem basis_equiv_dualBasis_apply {k M N ι : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [Fintype ι] [DecidableEq ι] (b' : Module.Basis ι k M)
    (b : Module.Basis ι k N) (w : M) (z : N) :
    (b'.equiv b.dualBasis (Equiv.refl ι)) w z = ∑ i, b'.repr w i * b.repr z i := by
  conv_lhs => rw [← b'.sum_repr w]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.equiv_apply, Equiv.refl_apply, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply, smul_eq_mul]

theorem baseChange_reductionBasis_repr {R : Type*} [CommRing R] (π : R) {M : Type*}
    [AddCommGroup M] [Module R M] {ι : Type*} (b : Module.Basis ι R M) (k' : Type*)
    [CommRing k'] [Algebra (R ⧸ Ideal.span {π}) k'] (y : M) (i : ι) :
    (Algebra.TensorProduct.basis k' (reductionBasis π b)).repr (1 ⊗ₜ Submodule.Quotient.mk y) i =
      algebraMap (R ⧸ Ideal.span {π}) k' (Ideal.Quotient.mk (Ideal.span {π}) (b.repr y i)) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
    reductionBasis_repr_mk]

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Group G]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem latticePairing_invariant (ρ : Representation K G V) (φ : V ≃ₗ[K] Module.Dual K V)
    (hφ : ∀ g v, φ (ρ g v) = ρ.dual g (φ v)) {L : Submodule R V}
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) [Module.Finite R L] (hsp : Submodule.span K (L : Set V) = ⊤)
    (e : Module.Basis ι R L) (g : G) (v : dualLattice (R := R) φ (latticeBasis hsp e))
    (x : L) :
    latticePairing (Module.Basis.span (dualLattice_linearIndependent φ (latticeBasis hsp e))) e
        ⟨ρ g v, dualLattice_invariant ρ φ hφ hL hsp e g v v.2⟩ x =
      latticePairing (Module.Basis.span (dualLattice_linearIndependent φ (latticeBasis hsp e))) e
        v ⟨ρ g⁻¹ x, hL g⁻¹ x x.2⟩ := by
  apply IsFractionRing.injective R K
  rw [algebraMap_latticePairing, algebraMap_latticePairing]
  change φ (ρ g v) x = φ v (ρ g⁻¹ x)
  rw [hφ, dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]

noncomputable def selfDualReductionEquiv (π : R) (ρ : Representation K G V)
    (φ : V ≃ₗ[K] Module.Dual K V) (hφ : ∀ g v, φ (ρ g v) = ρ.dual g (φ v))
    {L : Submodule R V} (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) (e : Module.Basis ι R L) (k' : Type*) [Field k']
    [Algebra (R ⧸ Ideal.span {π}) k'] :
    (baseChangeRepresentation k' (latticeReduction π ρ
        (dualLattice (R := R) φ (latticeBasis hsp e))
        (dualLattice_invariant ρ φ hφ hL hsp e))).Equiv
      (baseChangeRepresentation k' (latticeReduction π ρ L hL)).dual :=
  let fL := Module.Basis.span (dualLattice_linearIndependent (R := R) φ (latticeBasis hsp e))
  let bL := Algebra.TensorProduct.basis k' (reductionBasis π e)
  let bL' := Algebra.TensorProduct.basis k' (reductionBasis π fL)
  have hΨ : ∀ (v : dualLattice (R := R) φ (latticeBasis hsp e)) (x : L),
      (bL'.equiv bL.dualBasis (Equiv.refl ι)) (1 ⊗ₜ Submodule.Quotient.mk v)
        (1 ⊗ₜ Submodule.Quotient.mk x) =
      algebraMap (R ⧸ Ideal.span {π}) k'
        (Ideal.Quotient.mk (Ideal.span {π}) (latticePairing fL e v x)) := by
    intro v x
    rw [basis_equiv_dualBasis_apply, latticePairing, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [baseChange_reductionBasis_repr, baseChange_reductionBasis_repr, map_mul, map_mul]
  Representation.Equiv.mk (bL'.equiv bL.dualBasis (Equiv.refl ι)) fun g => by
    apply bL'.ext
    intro i
    apply bL.ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    simp only [bL', bL, Algebra.TensorProduct.basis_apply, reductionBasis_apply,
      baseChangeRepresentation_tmul, latticeReduction_apply_mk]
    rw [hΨ, hΨ]
    congr 2
    exact latticePairing_invariant ρ φ hφ hL hsp e g (fL i) (e j)

end Psi

section Main

universe w w' w''

variable {R K G V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Group G] [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]

theorem trivial_multiplicity_odd_of_selfDual {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) [CharP (R ⧸ Ideal.span {π}) 2] (hodd : Odd (Module.finrank K V))
    (φ : V ≃ₗ[K] Module.Dual K V) (hφ : ∀ g v, φ (ρ g v) = ρ.dual g (φ v))
    (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) [Module.Free R L] [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) (kbar : Type*) [Field kbar] [IsAlgClosed kbar]
    [Algebra (R ⧸ Ideal.span {π}) kbar] :
    0 < repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL))
        (Representation.trivial kbar G kbar) ∧
      Odd (repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL))
        (Representation.trivial kbar G kbar)) := by
  have : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  let e := Module.Free.chooseBasis R L
  have hL' := dualLattice_invariant ρ φ hφ hL hsp e
  have : Module.Finite R (dualLattice (R := R) φ (latticeBasis hsp e)) :=
    Module.Finite.span_of_finite R (Set.finite_range _)
  have hsp' := dualLattice_span_eq_top (R := R) φ (latticeBasis hsp e)
  have : CharP kbar 2 :=
    charP_of_injective_algebraMap (algebraMap (R ⧸ Ideal.span {π}) kbar).injective 2
  have hdim : Module.finrank kbar
      (kbar ⊗[R ⧸ Ideal.span {π}] (L ⧸ (Ideal.span {π} • ⊤ : Submodule R L))) =
      Module.finrank K V := by
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis kbar (reductionBasis π e)),
      Module.finrank_eq_card_basis (latticeBasis hsp e)]
  have hself : ∀ (W : Type _) [AddCommGroup W] [Module kbar W]
      (σ : Representation kbar G W), σ.IsIrreducible →
      repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL)) σ =
        repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL)).dual σ := by
    intro W _ _ σ _
    rw [repMultiplicity_baseChange_latticeReduction_eq hπ ρ hL hL' hsp hsp' kbar σ]
    exact repMultiplicity_congr_left (selfDualReductionEquiv π ρ φ hφ hL hsp e kbar) σ
  exact (self_dual_characteristic_two_composition_parity_forces_trivial_factor.{_, _, _, 0} _
    hself).2.1 (hdim ▸ hodd)

theorem DVR_lattice_reduction_independence_and_self_dual_odd_parity [FiniteDimensional K V]
    {π : R} (hπ : Irreducible π) (ρ : Representation K G V) :
    (∀ (L₁ L₂ : Submodule R V) (hL₁ : ∀ g, ∀ x ∈ L₁, ρ g x ∈ L₁)
        (hL₂ : ∀ g, ∀ x ∈ L₂, ρ g x ∈ L₂),
        Module.Free R L₁ → Module.Finite R L₁ → Submodule.span K (L₁ : Set V) = ⊤ →
        Module.Free R L₂ → Module.Finite R L₂ → Submodule.span K (L₂ : Set V) = ⊤ →
        (∀ (W : Type w) [AddCommGroup W] [Module (R ⧸ Ideal.span {π}) W]
          (σ : Representation (R ⧸ Ideal.span {π}) G W),
          repMultiplicity (latticeReduction π ρ L₁ hL₁) σ =
            repMultiplicity (latticeReduction π ρ L₂ hL₂) σ) ∧
        ∀ (k' : Type w') [Field k'] [Algebra (R ⧸ Ideal.span {π}) k'] (W : Type w)
          [AddCommGroup W] [Module k' W] (σ : Representation k' G W),
          repMultiplicity (baseChangeRepresentation k' (latticeReduction π ρ L₁ hL₁)) σ =
            repMultiplicity (baseChangeRepresentation k' (latticeReduction π ρ L₂ hL₂)) σ) ∧
    (CharP (R ⧸ Ideal.span {π}) 2 → Odd (Module.finrank K V) →
      ∀ φ : V ≃ₗ[K] Module.Dual K V, (∀ g v, φ (ρ g v) = ρ.dual g (φ v)) →
      ∀ (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L), Module.Free R L →
        Module.Finite R L → Submodule.span K (L : Set V) = ⊤ →
        ∀ (kbar : Type w'') [Field kbar] [IsAlgClosed kbar] [Algebra (R ⧸ Ideal.span {π}) kbar],
          0 < repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL))
              (Representation.trivial kbar G kbar) ∧
            Odd (repMultiplicity (baseChangeRepresentation kbar (latticeReduction π ρ L hL))
              (Representation.trivial kbar G kbar))) := by
  refine ⟨fun L₁ L₂ hL₁ hL₂ _ hfin₁ hsp₁ _ hfin₂ hsp₂ => ⟨fun W _ _ σ => ?_,
    fun k' _ _ W _ _ σ => ?_⟩, fun h2 hodd φ hφ L hL _ _ hsp kbar _ _ _ =>
      trivial_multiplicity_odd_of_selfDual hπ ρ hodd φ hφ L hL hsp kbar⟩
  · exact repMultiplicity_latticeReduction_eq hπ ρ hL₁ hL₂ hsp₁ hsp₂ σ
  · exact repMultiplicity_baseChange_latticeReduction_eq hπ ρ hL₁ hL₂ hsp₁ hsp₂ k' σ

theorem exists_fixed_mod_invariant_of_selfDual {π : R} (hπ : Irreducible π)
    (ρ : Representation K G V) [CharP (R ⧸ Ideal.span {π}) 2] (hodd : Odd (Module.finrank K V))
    (φ : V ≃ₗ[K] Module.Dual K V) (hφ : ∀ g v, φ (ρ g v) = ρ.dual g (φ v))
    (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) [Module.Free R L] [Module.Finite R L]
    (hsp : Submodule.span K (L : Set V) = ⊤) (kbar : Type*) [Field kbar] [IsAlgClosed kbar]
    [Algebra (R ⧸ Ideal.span {π}) kbar] :
    ∃ N : Submodule kbar
        (kbar ⊗[R ⧸ Ideal.span {π}] (L ⧸ (Ideal.span {π} • ⊤ : Submodule R L))),
      (∀ g, ∀ x ∈ N, baseChangeRepresentation kbar (latticeReduction π ρ L hL) g x ∈ N) ∧
      ∃ v ∉ N, ∀ g, baseChangeRepresentation kbar (latticeReduction π ρ L hL) g v - v ∈ N :=
  exists_invariant_fixed_mod_of_repMultiplicity_trivial_pos
    (trivial_multiplicity_odd_of_selfDual hπ ρ hodd φ hφ L hL hsp kbar).1

theorem latticeReduction_trivial_multiplicity_pos {G : Type*} [Group G] (R : Type*) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π) (E : Type*) [Field E]
    [Algebra R E] [IsFractionRing R E] (V : Type*) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] [Module R V] [IsScalarTower R E V] (ρ : Representation E G V)
    (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) :
    Module.Free R L → Module.Finite R L → Submodule.span E (L : Set V) = ⊤ →
    CharP (R ⧸ Ideal.span {π}) 2 → Odd (Module.finrank E V) →
    ∀ φ : V ≃ₗ[E] Module.Dual E V, (∀ g v, φ (ρ g v) = ρ.dual g (φ v)) →
    ∀ (K' : Type*) [Field K'] [IsAlgClosed K'] [Algebra (R ⧸ Ideal.span {π}) K'],
      0 < repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L hL))
        (Representation.trivial K' G K') := by
  intro _ _ hsp _ hodd φ hφ K' _ _ _
  exact (trivial_multiplicity_odd_of_selfDual hπ ρ hodd φ hφ L hL hsp K').1

end Main

end CFSG.Semidihedral.Principal
