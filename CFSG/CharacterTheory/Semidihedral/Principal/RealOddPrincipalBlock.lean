module

public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlockLattice
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.LatticeReductionParity
public import CFSG.CharacterTheory.Semidihedral.Principal.NumberFieldRealization

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Spectral

variable {G : Type*} [Group G] [Fintype G]

theorem asAlgebraHom_eq_sum_coeff {k W : Type*} [CommSemiring k] [AddCommMonoid W] [Module k W]
    (ρ : Representation k G W) (a : MonoidAlgebra k G) :
    ρ.asAlgebraHom a = ∑ g : G, a.coeff g • ρ g := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  apply Finsupp.sum_fintype
  intro g
  exact zero_smul k (ρ g)

theorem characterSubsetIdempotent_action_of_mem (basis : FiniteIrreducibleCharacterBasis G)
    (S : Finset basis.index) (T : FiniteComplexRepresentation G) (hT : T.IsIrreducible)
    {χ : basis.index} (hχ : (basis.representation χ).character = T.character) (hχS : χ ∈ S) :
    T.representation.asAlgebraHom (characterSubsetIdempotent basis S) = 1 := by
  rw [characterSubsetIdempotent,
    characterIdempotentExpansion_action_of_character_eq basis _ T hT hχ,
    ite_eq_left hχS, one_smul]

theorem characterSubsetIdempotent_augmentation (basis : FiniteIrreducibleCharacterBasis G)
    (S : Finset basis.index) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∑ g, (characterSubsetIdempotent basis S).coeff g = if principal ∈ S then 1 else 0 := by
  simp_rw [characterSubsetIdempotent_coeff]
  rw [Finset.sum_comm]
  have hterm : ∀ ψ : basis.index, ∑ g : G, (basis.representation ψ).character 1 /
      (Nat.card G : ℂ) * (basis.representation ψ).character g⁻¹ =
      if ψ = principal then 1 else 0 := by
    intro ψ
    have hpair := characterPairing_irreducible (basis.representation principal)
      (basis.representation ψ) (basis.irreducible principal) (basis.irreducible ψ)
    have hsum : ∑ g : G, (basis.representation ψ).character 1 / (Nat.card G : ℂ) *
        (basis.representation ψ).character g⁻¹ = (basis.representation ψ).character 1 *
          characterPairing (basis.representation principal).character
            (basis.representation ψ).character := by
      unfold characterPairing
      rw [hprincipal, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.one_apply, one_mul]
      ring
    rw [hsum, hpair]
    by_cases hψ : ψ = principal
    · subst hψ
      rw [ite_eq_left rfl, ite_eq_left rfl, mul_one, hprincipal]
      rfl
    · rw [ite_eq_right (fun h => hψ (basis.distinct h).symm), ite_eq_right hψ, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']

end Spectral

section Reduction

variable {G : Type*} [Group G]

theorem augmentation_eq_one_of_trivial_factor [Fintype G] {R E V : Type*} [CommRing R] [Field E]
    [Algebra R E] [AddCommGroup V] [Module E V] [Module R V] [IsScalarTower R E V]
    (K' : Type*) [Field K'] (π : R) [Algebra (R ⧸ Ideal.span {π}) K']
    (ρ : Representation E G V) (L : Submodule R V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L) (c : G → R)
    (hid : ∑ g, algebraMap R E (c g) • ρ g = LinearMap.id)
    (htriv : 0 < repMultiplicity (baseChangeRepresentation K' (latticeReduction π ρ L hL))
      (Representation.trivial K' G K')) :
    algebraMap (R ⧸ Ideal.span {π}) K' (Ideal.Quotient.mk (Ideal.span {π}) (∑ g, c g)) = 1 ∧
      Ideal.Quotient.mk (Ideal.span {π}) (∑ g, c g) ≠ 0 := by
  obtain ⟨N, -, v, hv, hfix⟩ := exists_invariant_fixed_mod_of_repMultiplicity_trivial_pos htriv
  have hL1 := sum_smul_submoduleRepresentation_eq_id ρ L hL c hid
  have hL2 := sum_reduceModIdeal_eq_id (Ideal.span {π}) (fun g => submoduleRepresentation ρ L hL g)
    c hL1
  have hL3 := sum_baseChange_eq_id (K' := K') _ _ hL2
  have hone : algebraMap (R ⧸ Ideal.span {π}) K' (Ideal.Quotient.mk (Ideal.span {π}) (∑ g, c g)) =
      1 := by
    rw [map_sum, map_sum]
    exact sum_eq_one_of_fixed_mod_submodule
      (fun g => baseChangeRepresentation K' (latticeReduction π ρ L hL) g) _ hL3 N hv hfix
  refine ⟨hone, fun h0 => ?_⟩
  rw [h0, map_zero] at hone
  exact zero_ne_one hone

end Reduction

section Realization

variable {G : Type} [Group G] [Fintype G]

theorem sum_smul_glRepresentation_eq_id {E : IntermediateField ℚ ℂ} {d : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) E) (c : G → E)
    (hc : ∑ g, ((c g : E) : ℂ) •
      glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ) g =
        LinearMap.id) :
    ∑ g, c g • glRepresentation ρ g = LinearMap.id := by
  have hmat : ∑ g, c g • (ρ g : Matrix (Fin d) (Fin d) E) = 1 := by
    apply Matrix.map_injective (algebraMap E ℂ).injective
    have h := congrArg LinearMap.toMatrix' hc
    rw [map_sum, LinearMap.toMatrix'_id] at h
    simp only [map_smul, glRepresentation_apply, LinearMap.toMatrix'_toLin'] at h
    show (∑ g, c g • (ρ g : Matrix (Fin d) (Fin d) E)).map (algebraMap E ℂ) =
      (1 : Matrix (Fin d) (Fin d) E).map (algebraMap E ℂ)
    rw [Matrix.map_one _ (map_zero _) (map_one _), ← h]
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul]
    rfl
  calc ∑ g, c g • glRepresentation ρ g =
      Matrix.toLin' (∑ g, c g • (ρ g : Matrix (Fin d) (Fin d) E)) := by
        rw [map_sum]
        simp only [map_smul, glRepresentation_apply]
    _ = LinearMap.id := by rw [hmat, Matrix.toLin'_one]

theorem real_valued_odd_degree_irreducible_mem_principal_two_block
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (χ : basis.index)
    (hreal : ∀ g, starRingEnd ℂ ((basis.representation χ).character g) =
      (basis.representation χ).character g)
    (hodd : Odd (Module.finrank ℂ (basis.representation χ).vector)) :
    χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  set Rm := localizedComplexIntegerRing ideal with hRm
  set B := coefficientBlock basis Rm χ with hB
  set e := characterSubsetIdempotent basis B with he
  have hadm : ∀ g, e.coeff g ∈ Rm := coefficientBlock_admissible basis Rm χ
  have hfrac : ∀ g, ∃ a b : ComplexAlgebraicIntegers, b ∉ ideal ∧
      e.coeff g = (a : ℂ) / (b : ℂ) := fun g =>
    (localizedComplexIntegerRing_mem_iff_fraction ideal _).mp (hadm g)
  choose a b hb hab using hfrac
  set S : Set ℂ := Set.range (fun g => (a g : ℂ)) ∪ Set.range (fun g => (b g : ℂ)) with hS
  have hSfin : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℚ s := by
    rintro s (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact ((a g).2.tower_top (A := ℚ)).isAlgebraic
    · exact ((b g).2.tower_top (A := ℚ)).isAlgebraic
  have hχirr : (basis.representation χ).character ∈ BlocksIrr G :=
    ⟨(basis.representation χ).vector, inferInstance, inferInstance, inferInstance,
      (basis.representation χ).representation, basis.irreducible χ, rfl⟩
  set d := Module.finrank ℂ (basis.representation χ).vector with hddef
  have hd : (d : ℂ) = (basis.representation χ).character 1 :=
    (Representation.char_one (basis.representation χ).representation).symm
  obtain ⟨-, hrealcase⟩ := complex_irreducible_and_self_duality_realize_over_number_field hχirr d
    hd S hSfin hSalg
  obtain ⟨E, ρ, hfd, hSE, hirr, hchar, φ, hφ⟩ := hrealcase hreal
  have : FiniteDimensional ℚ E := hfd
  have hcR : ∀ g, ∃ r : integerLocalRing E ideal, (((r : E) : ℂ)) = e.coeff g := fun g => by
    obtain ⟨r, hr⟩ := div_mem_integerLocalRing E ideal (a g) (b g) (hSE (Or.inl ⟨g, rfl⟩))
      (hSE (Or.inr ⟨g, rfl⟩)) (hb g)
    exact ⟨r, by rw [hr, hab]⟩
  choose c hc using hcR
  let T : FiniteComplexRepresentation G :=
    { vector := Fin d → ℂ
      representation := glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ) }
  have hact := characterSubsetIdempotent_action_of_mem basis B T hirr hchar.symm
    (coefficientBlock_self_mem _ _ _)
  rw [asAlgebraHom_eq_sum_coeff] at hact
  have hidE : ∑ g, ((c g : integerLocalRing E ideal) : E) • glRepresentation ρ g =
      LinearMap.id := by
    apply sum_smul_glRepresentation_eq_id ρ (fun g => (c g : E))
    have hc' : ∀ g, (((c g : integerLocalRing E ideal) : E) : ℂ) = e.coeff g := hc
    simp only [hc']
    exact hact
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integerLocalRing E ideal)
  have hmax : Ideal.span {π} = IsLocalRing.maximalIdeal (integerLocalRing E ideal) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ |>.symm
  have : (Ideal.span {π}).IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal _
  let : Field (integerLocalRing E ideal ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hchar2 : CharP (integerLocalRing E ideal ⧸ Ideal.span {π}) 2 := by
    rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
    have h2 : (2 : integerLocalRing E ideal) ∈ Ideal.span {π} := by
      rw [hmax]
      exact two_mem_maximalIdeal_integerLocalRing E ideal
    have := Ideal.Quotient.eq_zero_iff_mem.mpr h2
    exact_mod_cast this
  set b0 : Fin d → (Fin d → E) := fun i => Pi.single i 1 with hb0
  have hb0span : Submodule.span E (Set.range b0) = ⊤ := by
    have hfun : ⇑(Pi.basisFun E (Fin d)) = b0 := funext fun i => Pi.basisFun_apply E (Fin d) i
    rw [← hfun]
    exact (Pi.basisFun E (Fin d)).span_eq
  have hL := orbitLattice_invariant (R := integerLocalRing E ideal) (glRepresentation ρ) b0
  have htriv := latticeReduction_trivial_multiplicity_pos (integerLocalRing E ideal) π hπ E
    (Fin d → E) (glRepresentation ρ)
    (orbitLattice (integerLocalRing E ideal) (glRepresentation ρ) b0) hL
    (orbitLattice_free (glRepresentation ρ) b0) (orbitLattice_finite (glRepresentation ρ) b0)
    (span_orbitLattice (glRepresentation ρ) b0 hb0span) hchar2
    (by rw [Module.finrank_fin_fun]; exact hodd) φ hφ
    (AlgebraicClosure (integerLocalRing E ideal ⧸ Ideal.span {π}))
  have hne := (augmentation_eq_one_of_trivial_factor
    (AlgebraicClosure (integerLocalRing E ideal ⧸ Ideal.span {π})) π (glRepresentation ρ) _ hL c
    hidE htriv).2
  have haug := characterSubsetIdempotent_augmentation basis B principal hprincipal
  have hprin : principal ∈ B := by
    by_contra hnot
    rw [ite_eq_right hnot] at haug
    have h1 : algebraMap E ℂ ((integerLocalRing E ideal).val (∑ g, c g)) = ∑ g, e.coeff g := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun g _ => hc g
    rw [haug] at h1
    have hzero : (∑ g, c g : integerLocalRing E ideal) = 0 :=
      Subtype.ext ((algebraMap E ℂ).injective (h1.trans (map_zero _).symm))
    exact hne (by rw [hzero, map_zero])
  exact (coefficientBlock_mem_iff _ _ _ _).mpr
    (sameCoefficientBlock_symm _ _ ((coefficientBlock_mem_iff _ _ _ _).mp hprin))

end Realization

end CFSG.Semidihedral.Principal
