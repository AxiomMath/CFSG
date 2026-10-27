module

public import CFSG.Dihedral.Glauberman.DicksonMaxDown

public section

namespace CFSG.Glauberman.Dickson.MaxSubfield

open BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown
open Polynomial

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def fixField (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (k : ℕ) : Subfield F :=
  (RingHom.id F).eqLocusField (iterateFrobenius F p k)

omit [Finite F] in
theorem mem_fixField [CharP F p] {k : ℕ} {x : F} : x ∈ fixField F p k ↔ x ^ p ^ k = x := by
  rw [fixField, RingHom.mem_eqLocusField, RingHom.id_apply, iterateFrobenius_def, eq_comm]

omit [Finite F] in
theorem fixField_mono [CharP F p] {m k : ℕ} (h : m ∣ k) : fixField F p m ≤ fixField F p k := by
  intro x hx
  rw [mem_fixField] at hx ⊢
  obtain ⟨j, rfl⟩ := h
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

theorem le_fixField_of_card [CharP F p] {K : Subfield F} {m : ℕ} (hK : Nat.card K = p ^ m) :
    K ≤ fixField F p m := by
  intro x hx
  rw [mem_fixField]
  let : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card (⟨x, hx⟩ : K)
  rw [Fintype.card_eq_nat_card, hK] at h
  exact congrArg Subtype.val h

theorem card_fixField [CharP F p] (hF : Nat.card F = p ^ f) {k : ℕ} (hk : k ∣ f) (hk0 : k ≠ 0) :
    Nat.card (fixField F p k) = p ^ k := by
  classical
  let : Fintype F := Fintype.ofFinite F
  apply le_antisymm
  ·
    have hne : (X ^ p ^ k - X : F[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero F hk0 hp.out.one_lt
    have hdeg : (X ^ p ^ k - X : F[X]).natDegree = p ^ k :=
      FiniteField.X_pow_card_pow_sub_X_natDegree_eq F hk0 hp.out.one_lt
    let Z : Finset F := Finset.univ.filter (· ∈ fixField F p k)
    have hZ : Z.val ⊆ (X ^ p ^ k - X : F[X]).roots := by
      intro x hx
      have hx' : x ∈ Z := Finset.mem_val.mp hx
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot, eval_sub, eval_pow, eval_X,
        sub_eq_zero, ← mem_fixField]
      exact (Finset.mem_filter.mp hx').2
    have := Polynomial.card_le_degree_of_subset_roots hZ
    rw [hdeg] at this
    calc Nat.card (fixField F p k) = Fintype.card (fixField F p k) := Nat.card_eq_fintype_card
      _ = Z.card := Fintype.card_subtype _
      _ ≤ p ^ k := this
  ·
    obtain ⟨φ⟩ := CFSG.Glauberman.Dickson.nonempty_galoisField_ringHom hF hk
    have hle : φ.fieldRange ≤ fixField F p k := by
      rintro x ⟨y, rfl⟩
      rw [mem_fixField, ← map_pow]
      congr 1
      let : Fintype (GaloisField p k) := Fintype.ofFinite _
      have h := FiniteField.pow_card y
      rwa [Fintype.card_eq_nat_card, GaloisField.card p k hk0] at h
    have hcard : Nat.card φ.fieldRange = p ^ k := by
      rw [← GaloisField.card p k hk0]
      exact (Nat.card_congr (RingHom.rangeRestrictFieldEquiv φ).toEquiv).symm
    calc p ^ k = Nat.card φ.fieldRange := hcard.symm
      _ ≤ Nat.card (fixField F p k) := by
        let : Finite (fixField F p k) := inferInstance
        exact Nat.card_le_card_of_injective (Subfield.inclusion hle)
          (fun a b h => Subtype.ext (by
            have := congrArg Subtype.val h
            exact this))

end CFSG.Glauberman.Dickson.MaxSubfield

namespace CFSG.Glauberman.Dickson.MaxSubfield

open BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def pglImage (K : Subfield F) : Subgroup (PGL2 F) :=
  (h826_pglMap K.subtype).range

omit [Finite F] in
theorem pglImage_mono
    {K₀ K₁ : Subfield F} (h : K₀ ≤ K₁) : pglImage K₀ ≤ pglImage K₁ := by
  rintro x ⟨y, rfl⟩
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  refine ⟨Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (Subfield.inclusion h) A), ?_⟩
  rw [h826_pglMap_mk, h826_pglMap_mk]
  rfl

omit [Finite F] in
theorem card_pglImage
    (K : Subfield F) : Nat.card (pglImage K) = Nat.card (PGL2 K) :=
  (Nat.card_congr (MonoidHom.ofInjective
    (h826_pglMap_injective K.subtype K.subtype_injective)).toEquiv).symm

omit [Finite F] in
theorem h826_pslToPGL_eq_toPGL :
    (h826_pslToPGL : PSL2MatrixGroup F →* PGL2 F) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL := by
  apply QuotientGroup.monoidHom_ext
  ext A
  rfl

theorem toPGL_range_normal (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.Normal :=
  pslRange_normal hK hcard

@[expose] noncomputable def conjAut (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (c : PGL2 F) : PSL2MatrixGroup F ≃* PSL2MatrixGroup F :=
  haveI := toPGL_range_normal hK hcard
  (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
    ((MulAut.conjNormal c).trans
      (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm)

theorem toPGL_conjAut (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) (c : PGL2 F)
    (x : PSL2MatrixGroup F) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (conjAut hK hcard c x) =
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ := by
  have := toPGL_range_normal hK hcard
  simp only [conjAut, MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  simp [MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

@[expose] noncomputable def subfieldSubgroup (K : Subfield F) : Subgroup (PSL2MatrixGroup F) :=
  (pglImage K).comap Matrix.ProjectiveSpecialLinearGroup.toPGL

@[expose] noncomputable def overgroup (K : Subfield F) (c : PGL2 F) :
    Subgroup (PSL2MatrixGroup F) :=
  (pglImage K).comap ((MulAut.conj c).toMonoidHom.comp
    Matrix.ProjectiveSpecialLinearGroup.toPGL)

theorem overgroup_eq_comap (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (K : Subfield F) (c : PGL2 F) :
    overgroup K c = (subfieldSubgroup K).comap (conjAut hK hcard c).toMonoidHom := by
  ext x
  simp only [overgroup, subfieldSubgroup, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  rw [toPGL_conjAut]
  rfl

theorem card_overgroup (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (K : Subfield F) (c : PGL2 F) :
    Nat.card (overgroup K c) = Nat.card (subfieldSubgroup K) := by
  rw [overgroup_eq_comap hK hcard, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective (conjAut hK hcard c).symm.injective]

theorem card_subfieldSubgroup_le (K : Subfield F) :
    Nat.card (subfieldSubgroup K) ≤ Nat.card (PGL2 K) := by
  rw [← card_pglImage]
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Nat.card_le_card_of_injective
    (fun x => ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x, x.2⟩)
    (fun a b h => Subtype.ext (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (congrArg Subtype.val h)))

omit [Finite F] in
theorem psl2Map_mem_subfieldSubgroup
    (K : Subfield F) (y : PSL2MatrixGroup K) :
    CFSG.Glauberman.Dickson.psl2Map K.subtype y ∈ subfieldSubgroup K := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) y
  refine ⟨Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A), ?_⟩
  rw [h826_pglMap_mk, CFSG.Glauberman.Dickson.psl2Map_mk, QuotientGroup.mk'_apply,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  congr 1
  ext i j
  rfl

theorem card_subfieldSubgroup_ge (K : Subfield F) :
    Nat.card (PSL2MatrixGroup K) ≤ Nat.card (subfieldSubgroup K) :=
  Nat.card_le_card_of_injective
    (fun y => ⟨CFSG.Glauberman.Dickson.psl2Map K.subtype y, psl2Map_mem_subfieldSubgroup K y⟩)
    (fun _ _ h => CFSG.Glauberman.Dickson.psl2Map_injective K.subtype
      (congrArg Subtype.val h))

omit [Finite F] in
theorem pglImage_le_range
    (K : Subfield F) (hsq : ∀ x : K, IsSquare (x : F)) :
    pglImage K ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  rintro x ⟨y, rfl⟩
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [h826_pglMap_mk]
  obtain ⟨c, hc⟩ := hsq (A : Matrix (Fin 2) (Fin 2) K).det
  have hdet : ((Matrix.GeneralLinearGroup.map K.subtype A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = c * c := by
    have e1 : ((Matrix.GeneralLinearGroup.map K.subtype A : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = K.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [e1, ← RingHom.map_det, ← hc]
    rfl
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := (Matrix.GeneralLinearGroup.map K.subtype A).isUnit.map Matrix.detMonoidHom
    rw [Matrix.coe_detMonoidHom, hdet, h0, mul_zero] at h1
    exact not_isUnit_zero h1
  let B : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨c⁻¹ • ((Matrix.GeneralLinearGroup.map K.subtype A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F), by
      rw [Matrix.det_smul, hdet, Fintype.card_fin]
      field_simp⟩
  refine ⟨QuotientGroup.mk B, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext i j
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  change (c⁻¹ * _) * c = _
  field_simp

omit [Finite F] in
theorem card_subfieldSubgroup_eq
    (K : Subfield F) (hsq : ∀ x : K, IsSquare (x : F)) :
    Nat.card (subfieldSubgroup K) = Nat.card (PGL2 K) := by
  rw [← card_pglImage]
  exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (pglImage_le_range K hsq)))).toEquiv

omit [Finite F] in
theorem le_overgroup
    {M : Subgroup (PSL2MatrixGroup F)} {K₀ K : Subfield F} {c : PGL2 F}
    (hM : ∀ x ∈ M, c * Matrix.ProjectiveSpecialLinearGroup.toPGL x * c⁻¹ ∈ pglImage K₀)
    (hK : K₀ ≤ K) : M ≤ overgroup K c := by
  intro x hx
  exact pglImage_mono hK (hM x hx)

omit [Finite F] hp in
theorem le_overgroup_of_witness {M : Subgroup (PSL2MatrixGroup F)} {m : ℕ}
    (W : SubfieldConjugacyWitness p m M) :
    ∀ x ∈ M, W.conjugator * Matrix.ProjectiveSpecialLinearGroup.toPGL x * W.conjugator⁻¹ ∈
      pglImage W.K := by
  intro x hx
  refine ⟨W.phi ⟨x, hx⟩, ?_⟩
  rw [W.map_phi, h826_pslToPGL_eq_toPGL]

end CFSG.Glauberman.Dickson.MaxSubfield
