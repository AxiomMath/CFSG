module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import CFSG.Open.LocalVocabulary

public noncomputable section

open scoped BigOperators Classical TensorProduct NumberField

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Augmentation

theorem sum_eq_one_of_fixed_mod_submodule {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Fintype ι] (σ : ι → M →ₗ[K] M) (c : ι → K) (hid : ∑ i, c i • σ i = LinearMap.id)
    (N : Submodule K M) {v : M} (hv : v ∉ N) (hfix : ∀ i, σ i v - v ∈ N) :
    ∑ i, c i = 1 := by
  by_contra hne
  have hexp : v = ∑ i, c i • σ i v := by
    have h := congrArg (fun f : M →ₗ[K] M => f v) hid
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply] using h.symm
  have hmem : (1 - ∑ i, c i) • v ∈ N := by
    have heq : (1 - ∑ i, c i) • v = ∑ i, c i • (σ i v - v) := by
      simp only [smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul, Finset.sum_smul]
      rw [← hexp]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfix i)
  have hu : (1 - ∑ i, c i) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  exact hv ((Submodule.smul_mem_iff N hu).mp hmem)

end Augmentation

section Reduction

variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]

theorem sum_reduceModIdeal_eq_id (I : Ideal A) (f : ι → M →ₗ[A] M) (c : ι → A)
    (hid : ∑ i, c i • f i = LinearMap.id) :
    ∑ i, Ideal.Quotient.mk I (c i) • (f i).reduceModIdeal I = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have h := congrArg (fun F : M →ₗ[A] M => F x) hid
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
    simp only [LinearMap.reduceModIdeal_apply]
    conv_rhs => rw [← h]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.mkQ_apply]
    rfl

theorem sum_baseChange_eq_id {K K' N : Type*} [CommRing K] [CommRing K'] [Algebra K K']
    [AddCommGroup N] [Module K N] (f : ι → N →ₗ[K] N) (c : ι → K)
    (hid : ∑ i, c i • f i = LinearMap.id) :
    ∑ i, algebraMap K K' (c i) • (f i).baseChange K' = LinearMap.id := by
  have h : LinearMap.baseChangeHom K K' N N (∑ i, c i • f i) =
      LinearMap.baseChangeHom K K' N N LinearMap.id := congrArg _ hid
  rw [map_sum] at h
  simp only [map_smul, LinearMap.baseChangeHom_apply, LinearMap.baseChange_id] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_smul]

end Reduction

section Lattice

variable {G : Type*} [Group G] {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

@[expose] def orbitLattice (R : Type*) [CommRing R] [Algebra R E] [Module R V]
    [IsScalarTower R E V] (ρ : Representation E G V) {ι : Type*} (b : ι → V) : Submodule R V :=
  Submodule.span R (Set.range fun p : G × ι => ρ p.1 (b p.2))

variable {R : Type*} [CommRing R] [Algebra R E] [Module R V] [IsScalarTower R E V]

theorem orbitLattice_invariant (ρ : Representation E G V) {ι : Type*} (b : ι → V) (g : G) :
    ∀ x ∈ orbitLattice R ρ b, ρ g x ∈ orbitLattice R ρ b := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hy
    exact Submodule.subset_span ⟨⟨g * h, i⟩, by simp only [map_mul, Module.End.mul_apply]⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ r hx

theorem mem_orbitLattice (ρ : Representation E G V) {ι : Type*} (b : ι → V) (i : ι) :
    b i ∈ orbitLattice R ρ b :=
  Submodule.subset_span ⟨⟨1, i⟩, by simp⟩

theorem orbitLattice_finite [Finite G] (ρ : Representation E G V) {ι : Type*} [Finite ι]
    (b : ι → V) : Module.Finite R (orbitLattice R ρ b) :=
  Module.Finite.span_of_finite R (Set.finite_range _)

theorem span_orbitLattice (ρ : Representation E G V) {ι : Type*} (b : ι → V)
    (hb : Submodule.span E (Set.range b) = ⊤) :
    Submodule.span E (orbitLattice R ρ b : Set V) = ⊤ := by
  rw [eq_top_iff, ← hb]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span (mem_orbitLattice ρ b i)

theorem orbitLattice_free [IsDomain R] [IsPrincipalIdealRing R] [Module.IsTorsionFree R V]
    [Finite G] (ρ : Representation E G V) {ι : Type*} [Finite ι] (b : ι → V) :
    Module.Free R (orbitLattice R ρ b) := by
  have := orbitLattice_finite (R := R) ρ b
  infer_instance

@[expose] noncomputable def submoduleRepresentation (ρ : Representation E G V)
    (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) : Representation R G L where
  toFun g := ((ρ g).restrictScalars R).restrict (hL g)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Module.End.mul_apply]
    rfl

theorem submoduleRepresentation_apply (ρ : Representation E G V) (L : Submodule R V)
    (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (g : G) (x : L) :
    ((submoduleRepresentation ρ L hL g x : L) : V) = ρ g x := rfl

theorem sum_smul_submoduleRepresentation_eq_id [Fintype G] (ρ : Representation E G V)
    (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (r : G → R)
    (hid : ∑ g, algebraMap R E (r g) • ρ g = LinearMap.id) :
    ∑ g, r g • submoduleRepresentation ρ L hL g = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun F : V →ₗ[E] V => F (x : V)) hid
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, submoduleRepresentation_apply, algebraMap_smul] at h ⊢
  exact h

end Lattice

section NumberFieldLocalization

variable (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E]

instance intermediateField_numberField : NumberField E := ⟨⟩

@[expose] noncomputable def ringOfIntegersToAlgebraicIntegers :
    𝓞 E →+* ComplexAlgebraicIntegers where
  toFun x := ⟨((x : E) : ℂ), x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ E ℂ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [FiniteDimensional ℚ E] in
theorem ringOfIntegersToAlgebraicIntegers_coe (x : 𝓞 E) :
    ((ringOfIntegersToAlgebraicIntegers E x : ComplexAlgebraicIntegers) : ℂ) = ((x : E) : ℂ) :=
  rfl

omit [FiniteDimensional ℚ E] in
theorem exists_ringOfIntegers_of_mem (a : ComplexAlgebraicIntegers) (ha : (a : ℂ) ∈ E) :
    ∃ x : 𝓞 E, ringOfIntegersToAlgebraicIntegers E x = a := by
  have hint : IsIntegral ℤ (⟨(a : ℂ), ha⟩ : E) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E ℂ) (algebraMap E ℂ).injective]
    exact a.2
  exact ⟨⟨⟨(a : ℂ), ha⟩, hint⟩, rfl⟩

variable (ideal : Ideal ComplexAlgebraicIntegers)

@[expose] noncomputable def integerPrime : Ideal (𝓞 E) :=
  ideal.comap (ringOfIntegersToAlgebraicIntegers E)

instance integerPrime_isPrime [ideal.IsPrime] : (integerPrime E ideal).IsPrime :=
  Ideal.comap_isPrime _ _

omit [FiniteDimensional ℚ E] in
theorem two_mem_integerPrime [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    (2 : 𝓞 E) ∈ integerPrime E ideal := by
  rw [integerPrime, Ideal.mem_comap, map_ofNat]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_ofNat]
  exact_mod_cast CharP.cast_eq_zero (ComplexAlgebraicIntegers ⧸ ideal) 2

omit [FiniteDimensional ℚ E] in
theorem integerPrime_ne_bot [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    integerPrime E ideal ≠ ⊥ := by
  intro h
  have h2 := two_mem_integerPrime E ideal
  rw [h, Ideal.mem_bot] at h2
  exact two_ne_zero h2

@[expose] noncomputable def integerLocalRing [ideal.IsPrime] : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (integerPrime E ideal).primeCompl
    (integerPrime E ideal).primeCompl_le_nonZeroDivisors

instance integerLocalRing_isLocalization [ideal.IsPrime] :
    IsLocalization.AtPrime (integerLocalRing E ideal) (integerPrime E ideal) :=
  Localization.subalgebra.isLocalization_ofField _ _ _

instance integerLocalRing_isDiscreteValuationRing [ideal.IsPrime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    IsDiscreteValuationRing (integerLocalRing E ideal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E)
    (integerPrime_ne_bot E ideal) _

theorem div_mem_integerLocalRing [ideal.IsPrime] (a b : ComplexAlgebraicIntegers)
    (ha : (a : ℂ) ∈ E) (hb : (b : ℂ) ∈ E) (hbm : b ∉ ideal) :
    ∃ r : integerLocalRing E ideal, (((r : E) : ℂ)) = (a : ℂ) / (b : ℂ) := by
  obtain ⟨x, hx⟩ := exists_ringOfIntegers_of_mem E a ha
  obtain ⟨y, hy⟩ := exists_ringOfIntegers_of_mem E b hb
  have hyP : y ∈ (integerPrime E ideal).primeCompl := by
    change ¬ y ∈ ideal.comap (ringOfIntegersToAlgebraicIntegers E)
    rw [Ideal.mem_comap, hy]
    exact hbm
  refine ⟨⟨algebraMap (𝓞 E) E x * (algebraMap (𝓞 E) E y)⁻¹, x, y, hyP, rfl⟩, ?_⟩
  rw [div_eq_mul_inv, ← hx, ← hy]
  rfl

theorem two_mem_maximalIdeal_integerLocalRing [ideal.IsPrime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    (2 : integerLocalRing E ideal) ∈ IsLocalRing.maximalIdeal (integerLocalRing E ideal) := by
  have h := (IsLocalization.AtPrime.to_map_mem_maximal_iff (integerLocalRing E ideal)
    (integerPrime E ideal) 2).mpr (two_mem_integerPrime E ideal)
  rwa [map_ofNat] at h

end NumberFieldLocalization

end CFSG.Semidihedral.Principal
