module

public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

@[expose] noncomputable def glRepresentation {G R : Type*} [Group G] [CommRing R] {d : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) : Representation R G (Fin d → R) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

theorem glRepresentation_apply {G R : Type*} [Group G] [CommRing R] {d : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (g : G) :
    glRepresentation ρ g = Matrix.toLin' (ρ g : Matrix (Fin d) (Fin d) R) := rfl

theorem glRepresentation_character {G R : Type*} [Group G] [Field R] {d : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (g : G) :
    (glRepresentation ρ).character g = (ρ g : Matrix (Fin d) (Fin d) R).trace := by
  change LinearMap.trace R (Fin d → R) (Matrix.toLin' (ρ g : Matrix (Fin d) (Fin d) R)) = _
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin d)), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin']

abbrev AlgNum : Type := algebraicClosure ℚ ℂ

instance : IsAlgClosed AlgNum := IsAlgClosure.isAlgClosed ℚ

theorem exists_algebraic_zero_of_complex_zero {σ : Type*} [Finite σ]
    (P : Set (MvPolynomial σ AlgNum)) (z : σ → ℂ) (hz : ∀ p ∈ P, MvPolynomial.aeval z p = 0) :
    ∃ x : σ → AlgNum, ∀ p ∈ P, MvPolynomial.aeval x p = 0 := by
  set I := Ideal.span P
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial σ AlgNum) ∈ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
      have hle : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
        rw [Ideal.span_le]
        intro p hp
        exact hz p hp
      exact hle (htop ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal AlgNum hJ
  refine ⟨x, fun p hp => ?_⟩
  have hpJ : p ∈ J := hIJ (Ideal.subset_span hp)
  rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpJ
  exact hpJ

section Equations

abbrev RealizationVar (G : Type) (d : ℕ) : Type := (G × Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ Unit)

variable {G : Type} [Group G] [Fintype G] {d : ℕ}

@[expose] noncomputable def realizationX (g : G) :
    Matrix (Fin d) (Fin d) (MvPolynomial (RealizationVar G d) AlgNum) :=
  fun i j => MvPolynomial.X (Sum.inl (g, i, j))

@[expose] noncomputable def realizationY :
    Matrix (Fin d) (Fin d) (MvPolynomial (RealizationVar G d) AlgNum) :=
  fun i j => MvPolynomial.X (Sum.inr (Sum.inl (i, j)))

@[expose] noncomputable def realizationU : MvPolynomial (RealizationVar G d) AlgNum :=
  MvPolynomial.X (Sum.inr (Sum.inr ()))

@[expose] def representationEquations (c : G → AlgNum) :
    Set (MvPolynomial (RealizationVar G d) AlgNum) :=
  {p | (∃ (g h : G) (i j : Fin d), p = (realizationX (d := d) g * realizationX (d := d) h) i j -
      realizationX (d := d) (g * h) i j) ∨
    (∃ i j : Fin d, p = realizationX (d := d) (1 : G) i j -
      (1 : Matrix (Fin d) (Fin d) (MvPolynomial (RealizationVar G d) AlgNum)) i j) ∨
    ∃ g : G, p = (realizationX (d := d) g).trace - MvPolynomial.C (c g)}

@[expose] def formEquations : Set (MvPolynomial (RealizationVar G d) AlgNum) :=
  {p | (∃ (g : G) (i j : Fin d), p = ((realizationX (d := d) g).transpose *
      realizationY (G := G) (d := d) * realizationX (d := d) g) i j -
        realizationY (G := G) (d := d) i j) ∨
    p = realizationU (G := G) (d := d) * (realizationY (G := G) (d := d)).det - 1}

@[expose] def pointMatrix {R : Type*} (z : RealizationVar G d → R) (g : G) :
    Matrix (Fin d) (Fin d) R :=
  fun i j => z (Sum.inl (g, i, j))

@[expose] def pointForm {R : Type*} (z : RealizationVar G d → R) : Matrix (Fin d) (Fin d) R :=
  fun i j => z (Sum.inr (Sum.inl (i, j)))

variable {R : Type*} [CommRing R] [Algebra AlgNum R]

omit [Group G] [Fintype G] in
theorem map_realizationX (z : RealizationVar G d → R) (g : G) :
    (realizationX g).map (MvPolynomial.aeval z) = pointMatrix z g := by
  ext i j
  simp [realizationX, pointMatrix]

omit [Group G] [Fintype G] in
theorem map_realizationY (z : RealizationVar G d → R) :
    (realizationY (G := G) (d := d)).map (MvPolynomial.aeval z) = pointForm z := by
  ext i j
  simp [realizationY, pointForm]

omit [Group G] [Fintype G] in
theorem aeval_matrix_mul (z : RealizationVar G d → R)
    (A B : Matrix (Fin d) (Fin d) (MvPolynomial (RealizationVar G d) AlgNum)) (i j : Fin d) :
    MvPolynomial.aeval z ((A * B) i j) =
      (A.map (MvPolynomial.aeval z) * B.map (MvPolynomial.aeval z)) i j := by
  rw [← Matrix.map_mul]
  rfl

omit [Fintype G] in
theorem representationEquations_iff (c : G → AlgNum) (z : RealizationVar G d → R) :
    (∀ p ∈ representationEquations (d := d) c, MvPolynomial.aeval z p = 0) ↔
      (∀ g h, pointMatrix z g * pointMatrix z h = pointMatrix z (g * h)) ∧
        pointMatrix z 1 = 1 ∧ ∀ g, (pointMatrix z g).trace = algebraMap AlgNum R (c g) := by
  constructor
  · intro h
    refine ⟨fun g k => ?_, ?_, fun g => ?_⟩
    · ext i j
      have e := h _ (Or.inl ⟨g, k, i, j, rfl⟩)
      rw [map_sub, aeval_matrix_mul, map_realizationX, map_realizationX] at e
      have e2 : MvPolynomial.aeval z (realizationX (d := d) (g * k) i j) =
          pointMatrix z (g * k) i j := by
        simp [realizationX, pointMatrix]
      rw [e2] at e
      exact sub_eq_zero.mp e
    · ext i j
      have e := h _ (Or.inr (Or.inl ⟨i, j, rfl⟩))
      rw [map_sub] at e
      have e1 : MvPolynomial.aeval z (realizationX (d := d) (1 : G) i j) = pointMatrix z 1 i j := by
        simp [realizationX, pointMatrix]
      have e2 : MvPolynomial.aeval z ((1 : Matrix (Fin d) (Fin d) (MvPolynomial _ AlgNum)) i j) =
          (1 : Matrix (Fin d) (Fin d) R) i j := by
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      rw [e1, e2] at e
      exact sub_eq_zero.mp e
    · have e := h _ (Or.inr (Or.inr ⟨g, rfl⟩))
      rw [map_sub, AddMonoidHom.map_trace (MvPolynomial.aeval z), MvPolynomial.aeval_C,
        map_realizationX] at e
      exact sub_eq_zero.mp e
  · rintro ⟨hmul, hone, htr⟩ p (⟨g, k, i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨g, rfl⟩)
    · rw [map_sub, aeval_matrix_mul, map_realizationX, map_realizationX, hmul, sub_eq_zero]
      simp [realizationX, pointMatrix]
    · rw [map_sub, sub_eq_zero]
      have e1 : MvPolynomial.aeval z (realizationX (d := d) (1 : G) i j) = pointMatrix z 1 i j := by
        simp [realizationX, pointMatrix]
      rw [e1, hone]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    · rw [map_sub, AddMonoidHom.map_trace (MvPolynomial.aeval z), MvPolynomial.aeval_C,
        map_realizationX, htr, sub_self]

omit [Group G] [Fintype G] in
theorem formEquations_iff (z : RealizationVar G d → R) :
    (∀ p ∈ formEquations (G := G) (d := d), MvPolynomial.aeval z p = 0) ↔
      (∀ g, (pointMatrix z g).transpose * pointForm z * pointMatrix z g = pointForm z) ∧
        z (Sum.inr (Sum.inr ())) * (pointForm z).det = 1 := by
  have hT : ∀ g : G, (realizationX (d := d) g).transpose.map (MvPolynomial.aeval z) =
      (pointMatrix z g).transpose := fun g => by
    rw [Matrix.transpose_map, map_realizationX]
  have hY : ∀ i j : Fin d, MvPolynomial.aeval z (realizationY (G := G) (d := d) i j) =
      pointForm z i j := fun i j => by simp [realizationY, pointForm]
  have hU : MvPolynomial.aeval z (realizationU (G := G) (d := d)) = z (Sum.inr (Sum.inr ())) := by
    simp [realizationU]
  have hdet : MvPolynomial.aeval z (realizationY (G := G) (d := d)).det = (pointForm z).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_realizationY]
  have hentry : ∀ (g : G) (i j : Fin d),
      MvPolynomial.aeval z (((realizationX (d := d) g).transpose *
        realizationY (G := G) (d := d) * realizationX (d := d) g) i j) =
      ((pointMatrix z g).transpose * pointForm z * pointMatrix z g) i j := fun g i j => by
    rw [aeval_matrix_mul, Matrix.map_mul, hT, map_realizationY, map_realizationX]
  constructor
  · intro h
    refine ⟨fun g => ?_, ?_⟩
    · ext i j
      have e := h _ (Or.inl ⟨g, i, j, rfl⟩)
      rw [map_sub, hentry, hY] at e
      exact sub_eq_zero.mp e
    · have e := h _ (Or.inr rfl)
      rw [map_sub, map_mul, hU, hdet, map_one] at e
      exact sub_eq_zero.mp e
  · rintro ⟨hinv, hu⟩ p (⟨g, i, j, rfl⟩ | rfl)
    · rw [map_sub, hentry, hY, hinv, sub_self]
    · rw [map_sub, map_mul, hU, hdet, map_one, hu, sub_self]

end Equations

section Realization

variable {G : Type} [Group G] [Fintype G] {d : ℕ}

theorem exists_numberField_realization (c : G → AlgNum) (S : Set ℂ) (hSfin : S.Finite)
    (hS : ∀ s ∈ S, IsAlgebraic ℚ s) (x : RealizationVar G d → AlgNum)
    (hx : ∀ p ∈ representationEquations (d := d) c, MvPolynomial.aeval x p = 0) :
    let E := IntermediateField.adjoin ℚ (S ∪ Set.range fun v => ((x v : AlgNum) : ℂ))
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin d) E,
      FiniteDimensional ℚ E ∧ S ⊆ E ∧
      (∀ g, (ρ g : Matrix (Fin d) (Fin d) E).map (algebraMap E ℂ) =
        (pointMatrix x g).map (algebraMap AlgNum ℂ)) ∧
      ∀ v, ((x v : AlgNum) : ℂ) ∈ E := by
  intro E
  obtain ⟨hmul, hone, -⟩ := (representationEquations_iff c x).mp hx
  have hfinite : (S ∪ Set.range fun v => ((x v : AlgNum) : ℂ)).Finite :=
    hSfin.union (Set.finite_range _)
  have : Finite ↥(S ∪ Set.range fun v => ((x v : AlgNum) : ℂ)) := hfinite.to_subtype
  have hfd : FiniteDimensional ℚ E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro y (hy | ⟨v, rfl⟩)
    · exact (hS y hy).isIntegral
    · exact (mem_algebraicClosure_iff.mp (x v).2).isIntegral
  have hmemE : ∀ v, ((x v : AlgNum) : ℂ) ∈ E := fun v =>
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨v, rfl⟩)
  let ME : G → Matrix (Fin d) (Fin d) E := fun g i j => ⟨_, hmemE (Sum.inl (g, i, j))⟩
  have hMEmap : ∀ g, (ME g).map (algebraMap E ℂ) = (pointMatrix x g).map (algebraMap AlgNum ℂ) :=
    fun g => by
      ext i j
      rfl
  have hinj : Function.Injective fun M : Matrix (Fin d) (Fin d) E => M.map (algebraMap E ℂ) :=
    Matrix.map_injective (algebraMap E ℂ).injective
  have hMEmul : ∀ g h, ME g * ME h = ME (g * h) := by
    intro g h
    apply hinj
    simp only
    rw [Matrix.map_mul, hMEmap, hMEmap, hMEmap, ← Matrix.map_mul, hmul]
  have hMEone : ME 1 = 1 := by
    apply hinj
    simp only
    rw [hMEmap, hone, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  let ρ : G →* Matrix.GeneralLinearGroup (Fin d) E :=
    { toFun := fun g => ⟨ME g, ME g⁻¹, by rw [hMEmul, mul_inv_cancel, hMEone],
        by rw [hMEmul, inv_mul_cancel, hMEone]⟩
      map_one' := Units.ext hMEone
      map_mul' := fun g h => Units.ext (hMEmul g h).symm }
  refine ⟨ρ, hfd, fun s hs => IntermediateField.subset_adjoin ℚ _ (Or.inl hs), fun g => hMEmap g,
    hmemE⟩

omit [Fintype G] in
theorem glRepresentation_map_character {E : IntermediateField ℚ ℂ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) E) (g : G) :
    (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ)).character g =
      ((ρ g : Matrix (Fin d) (Fin d) E).map (algebraMap E ℂ)).trace := by
  rw [glRepresentation_character]
  rfl

omit [Fintype G] in
theorem exists_dual_equiv_of_invariant_form {E : Type*} [Field E]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) E) (Y : Matrix (Fin d) (Fin d) E)
    (hY : ∀ g, (ρ g : Matrix (Fin d) (Fin d) E).transpose * Y *
      (ρ g : Matrix (Fin d) (Fin d) E) = Y)
    (hdet : Y.det ≠ 0) :
    ∃ φ : (Fin d → E) ≃ₗ[E] Module.Dual E (Fin d → E),
      ∀ g v, φ (glRepresentation ρ g v) = (glRepresentation ρ).dual g (φ v) := by
  have hnd := (Matrix.nondegenerate_of_det_ne_zero hdet).toBilin'
  refine ⟨(Matrix.toBilin' Y).toDual hnd, fun g v => ?_⟩
  refine LinearMap.ext fun w => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Matrix.toBilin'_apply',
    Matrix.toBilin'_apply', glRepresentation_apply, glRepresentation_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply]
  set A := (ρ g : Matrix (Fin d) (Fin d) E)
  set A' := (ρ g⁻¹ : Matrix (Fin d) (Fin d) E)
  have hAA' : A * A' = 1 := by
    change ((ρ g * ρ g⁻¹ : Matrix.GeneralLinearGroup (Fin d) E) : Matrix (Fin d) (Fin d) E) = 1
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hkey : A.transpose * Y = Y * A' := by
    calc A.transpose * Y = A.transpose * Y * (A * A') := by rw [hAA', Matrix.mul_one]
      _ = (A.transpose * Y * A) * A' := by simp only [Matrix.mul_assoc]
      _ = Y * A' := by rw [hY g]
  have h1 : v ⬝ᵥ (A.transpose.mulVec (Y.mulVec w)) = (A.mulVec v) ⬝ᵥ (Y.mulVec w) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  calc (A.mulVec v) ⬝ᵥ (Y.mulVec w) = v ⬝ᵥ (A.transpose.mulVec (Y.mulVec w)) := h1.symm
    _ = v ⬝ᵥ ((A.transpose * Y).mulVec w) := by rw [Matrix.mulVec_mulVec]
    _ = v ⬝ᵥ (Y.mulVec (A'.mulVec w)) := by rw [hkey, Matrix.mulVec_mulVec]

theorem complex_irreducible_and_self_duality_realize_over_number_field {χ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) (d : ℕ) (hd : (d : ℂ) = χ 1) (S : Set ℂ) (hSfin : S.Finite)
    (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    (∃ (E : IntermediateField ℚ ℂ) (ρ : G →* Matrix.GeneralLinearGroup (Fin d) E),
      FiniteDimensional ℚ E ∧ S ⊆ E ∧
      (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ)).IsIrreducible ∧
      (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ)).character =
        χ) ∧
    ((∀ g, starRingEnd ℂ (χ g) = χ g) →
      ∃ (E : IntermediateField ℚ ℂ) (ρ : G →* Matrix.GeneralLinearGroup (Fin d) E),
        FiniteDimensional ℚ E ∧ S ⊆ E ∧
        (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ)).IsIrreducible ∧
        (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρ)).character =
          χ ∧
        ∃ φ : (Fin d → E) ≃ₗ[E] Module.Dual E (Fin d → E),
          ∀ g v, φ (glRepresentation ρ g v) = (glRepresentation ρ).dual g (φ v)) := by
  have hχ0 := hχ
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := hχ
  have hfin : Module.finrank ℂ V = d := by
    have h1 := Representation.char_one ρ
    rw [hchar, ← hd] at h1
    exact_mod_cast h1.symm
  let b := Module.finBasisOfFinrankEq ℂ V hfin
  let M : G → Matrix (Fin d) (Fin d) ℂ := fun g => LinearMap.toMatrix b b (ρ g)
  have hMmul : ∀ g h, M g * M h = M (g * h) := fun g h => by
    simp only [M, ← LinearMap.toMatrix_mul, map_mul]
  have hMone : M 1 = 1 := by
    simp only [M, map_one, LinearMap.toMatrix_one]
  have hMtr : ∀ g, (M g).trace = χ g := fun g => by
    rw [← hchar]
    exact (LinearMap.trace_eq_matrix_trace ℂ b (ρ g)).symm
  have hχalg : ∀ g, χ g ∈ algebraicClosure ℚ ℂ := fun g => by
    rw [mem_algebraicClosure_iff, ← hchar]
    exact (Representation.isIntegral_character ρ g).tower_top.isAlgebraic
  let c : G → AlgNum := fun g => ⟨χ g, hχalg g⟩
  have hreal : ∀ z : RealizationVar G d → ℂ, (∀ g, pointMatrix z g = M g) →
      ∀ p ∈ representationEquations (d := d) c, MvPolynomial.aeval z p = 0 := by
    intro z hz
    refine (representationEquations_iff c z).mpr ⟨fun g h => ?_, ?_, fun g => ?_⟩
    · rw [hz, hz, hz, hMmul]
    · rw [hz, hMone]
    · rw [hz, hMtr]
      rfl
  have hfinish : ∀ x : RealizationVar G d → AlgNum,
      (∀ p ∈ representationEquations (d := d) c, MvPolynomial.aeval x p = 0) →
      ∀ (E : IntermediateField ℚ ℂ) (ρE : G →* Matrix.GeneralLinearGroup (Fin d) E),
        (∀ g, (ρE g : Matrix (Fin d) (Fin d) E).map (algebraMap E ℂ) =
          (pointMatrix x g).map (algebraMap AlgNum ℂ)) →
        (glRepresentation ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρE)).character =
            χ ∧
          (glRepresentation
            ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρE)).IsIrreducible := by
    intro x hx E ρE hρE
    obtain ⟨-, -, htr⟩ := (representationEquations_iff c x).mp hx
    have hcharE : (glRepresentation
        ((Matrix.GeneralLinearGroup.map (algebraMap E ℂ)).comp ρE)).character = χ := by
      funext g
      rw [glRepresentation_map_character, hρE, ← AddMonoidHom.map_trace (algebraMap AlgNum ℂ),
        htr]
      rfl
    refine ⟨hcharE, ?_⟩
    apply CFSG.Wreathed.isIrreducible_of_character_mem_blocksIrr
    rw [hcharE]
    exact hχ0
  refine ⟨?_, fun hrealχ => ?_⟩
  ·
    let z : RealizationVar G d → ℂ := Sum.elim (fun t => M t.1 t.2.1 t.2.2) fun _ => 0
    obtain ⟨x, hx⟩ := exists_algebraic_zero_of_complex_zero _ z (hreal z fun g => rfl)
    obtain ⟨ρE, hfd, hSE, hρE, -⟩ := exists_numberField_realization c S hSfin hS x hx
    obtain ⟨hcharE, hirrE⟩ := hfinish x hx _ ρE hρE
    exact ⟨_, ρE, hfd, hSE, hirrE, hcharE⟩
  ·
    have hdualchar : ρ.dual.character = χ := by
      funext g
      rw [Representation.char_dual, hchar, ← blocksVChar_conjugate_inverse
        (AddSubgroup.subset_closure hχ0) g, hrealχ g]
    have : ρ.IsIrreducible := hirr
    have hdualirr : ρ.dual.IsIrreducible := by
      apply CFSG.Wreathed.isIrreducible_of_character_mem_blocksIrr
      rw [hdualchar]
      exact hχ0
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hequiv : Nonempty (Representation.Equiv ρ.dual ρ) := by
      have h1 := Representation.char_orthonormal ρ ρ.dual
      have h2 := Representation.char_orthonormal ρ ρ
      rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at h2
      rw [hdualchar, ← hchar, h2] at h1
      by_contra hne
      simp only [hne] at h1
      exact one_ne_zero h1
    let ψ : Representation.Equiv ρ ρ.dual := (Classical.choice hequiv).symm
    let B : LinearMap.BilinForm ℂ V := ψ.toLinearEquiv.toLinearMap
    have hBinv : ∀ g, B.comp (ρ g) (ρ g) = B := by
      intro g
      refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
      change ψ (ρ g v) (ρ g w) = ψ v w
      have hint : ψ (ρ g v) = ρ.dual g (ψ v) :=
        Representation.IntertwiningMap.isIntertwining ρ ρ.dual ψ.toIntertwiningMap g v
      rw [hint, Representation.dual_apply,
        Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hBnd : B.Nondegenerate := by
      refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun m hm => ?_
      have h0 : ψ m = 0 := LinearMap.ext fun n => hm n
      exact ψ.toLinearEquiv.injective (h0.trans (map_zero ψ).symm)
    let Y := LinearMap.BilinForm.toMatrix b B
    have hYinv : ∀ g, (M g).transpose * Y * M g = Y := by
      intro g
      have h := LinearMap.BilinForm.toMatrix_comp b b B (ρ g) (ρ g)
      rw [hBinv g] at h
      exact h.symm
    have hYdet : Y.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hBnd
    let z : RealizationVar G d → ℂ :=
      Sum.elim (fun t => M t.1 t.2.1 t.2.2) (Sum.elim (fun t => Y t.1 t.2) fun _ => Y.det⁻¹)
    have hzform : ∀ p ∈ formEquations (G := G) (d := d), MvPolynomial.aeval z p = 0 :=
      (formEquations_iff z).mpr ⟨fun g => hYinv g, inv_mul_cancel₀ hYdet⟩
    obtain ⟨x, hx⟩ := exists_algebraic_zero_of_complex_zero
      (representationEquations (d := d) c ∪ formEquations (G := G) (d := d)) z
      (fun p hp => hp.elim (hreal z (fun g => rfl) p) (hzform p))
    have hxrep : ∀ p ∈ representationEquations (d := d) c, MvPolynomial.aeval x p = 0 :=
      fun p hp => hx p (Or.inl hp)
    have hxform : ∀ p ∈ formEquations (G := G) (d := d), MvPolynomial.aeval x p = 0 :=
      fun p hp => hx p (Or.inr hp)
    obtain ⟨hxinv, hxdet⟩ := (formEquations_iff x).mp hxform
    let E : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ (S ∪ Set.range fun v => ((x v : AlgNum) : ℂ))
    obtain ⟨ρE, hfd, hSE, hρE, hmemE⟩ := exists_numberField_realization c S hSfin hS x hxrep
    obtain ⟨hcharE, hirrE⟩ := hfinish x hxrep E ρE hρE
    let YE : Matrix (Fin d) (Fin d) E := fun i j => ⟨_, hmemE (Sum.inr (Sum.inl (i, j)))⟩
    let uE : E := ⟨_, hmemE (Sum.inr (Sum.inr ()))⟩
    have hYEmap : YE.map (algebraMap E ℂ) = (pointForm x).map (algebraMap AlgNum ℂ) := by
      ext i j
      rfl
    have hinj : Function.Injective fun A : Matrix (Fin d) (Fin d) E => A.map (algebraMap E ℂ) :=
      Matrix.map_injective (algebraMap E ℂ).injective
    have hYEinv : ∀ g, (ρE g : Matrix (Fin d) (Fin d) E).transpose * YE *
        (ρE g : Matrix (Fin d) (Fin d) E) = YE := by
      intro g
      apply hinj
      simp only
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hρE, hYEmap,
        ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hxinv g]
    have hYEdet : YE.det ≠ 0 := by
      intro h0
      have h1 : algebraMap E ℂ (uE * YE.det) = algebraMap AlgNum ℂ
          (x (Sum.inr (Sum.inr ())) * (pointForm x).det) := by
        rw [map_mul, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, hYEmap,
          RingHom.map_det, RingHom.mapMatrix_apply]
        rfl
      rw [hxdet, h0, mul_zero, map_zero, map_one] at h1
      exact zero_ne_one h1
    obtain ⟨φ, hφ⟩ := exists_dual_equiv_of_invariant_form ρE YE hYEinv hYEdet
    exact ⟨E, ρE, hfd, hSE, hirrE, hcharE, φ, hφ⟩

end Realization

end CFSG.Semidihedral.Principal
