module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusEmbed
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTablesSp6
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus
  commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_involutions_conjugate_into_semilinear_image)

variable (k : Type) [Field k] {b c : k}

theorem quadMinus_minusVec : quadMinus 4 k b c (minusVec k) = 1 := by
  rw [coe_quadMinus]
  exact statedQuadMinus_minusVec k b c

theorem reindexQuadraticForm_minus_minusVec :
    reindexQuadraticForm (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c)
      (reindexVectorEquiv (minusIndexEquiv 4 (by norm_num)) (minusVec k)) = 1 := by
  rw [reindexQuadraticForm_reindexVectorEquiv, quadMinus_minusVec]

variable [CharP k 2]

variable (b c) in
theorem matrixDerivedScalars_omegaMinus_eq_bot :
    matrixDerivedScalars (reindexQuadraticForm (minusIndexEquiv 4 (by norm_num))
      (quadMinus 4 k b c)) = ⊥ :=
  LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo _
    ⟨_, by rw [reindexQuadraticForm_minus_minusVec]; exact one_ne_zero⟩

variable (b c) in
@[expose] noncomputable def omegaMinusBetaC : MulAut (StatedOmega (StatedQuadMinus 4 k b c)) :=
  omegaSymmetryAut (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c) (coe_quadMinus 4 k b c)
    (matrixDerivedScalars_omegaMinus_eq_bot k b c) (minusVec k)

theorem ne_zero_of_irreducible [Finite k] (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) c
  apply hirr s
  rw [hs, zero_mul, add_zero, ← sq, CharTwo.add_self_eq_zero]

theorem mem_fixedSubgroup_omegaMinusBetaC_iff [Finite k] (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (A : StatedOmega (StatedQuadMinus 4 k b c)) :
    A ∈ fixedSubgroup (omegaMinusBetaC k b c) ↔
      ((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ minusVec k = minusVec k :=
  mem_fixedSubgroup_omegaSymmetryAut_iff _ _ _ _ _
    (regular_coordinateQuadMinus 4 k b c le_rfl hirr).1 (quadMinus_minusVec k) A

omit [CharP k 2] in
theorem isometry_of_mem_omegaMinus8 (A : StatedOmega (StatedQuadMinus 4 k b c))
    (x : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    StatedQuadMinus 4 k b c (((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
      Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ x) =
        StatedQuadMinus 4 k b c x := by
  have h1 : (A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) ∈ Subgroup.closure
      {A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k | ∀ v, StatedQuadMinus 4 k b c
        (((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
          Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ
          v) = StatedQuadMinus 4 k b c v} :=
    Subgroup.commutator_le_self _ A.2
  rw [ClassicalGroups.Orthogonal.closure_isometries_eq_comap (coe_quadMinus 4 k b c),
    Subgroup.mem_comap] at h1
  have h2 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h1 x
  rwa [MulEquiv.coe_toMonoidHom, ClassicalGroups.Orthogonal.toLinEquiv_apply,
    coe_quadMinus] at h2

theorem coe_mem_minusStab [Finite k] (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {A : StatedOmega (StatedQuadMinus 4 k b c)} (hA : A ∈ fixedSubgroup (omegaMinusBetaC k b c)) :
    (A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) ∈ minusStab k b c :=
  ⟨isometry_of_mem_omegaMinus8 k A, (mem_fixedSubgroup_omegaMinusBetaC_iff k hirr A).1 hA⟩

@[expose] noncomputable def omegaMinusRes [Finite k] (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    fixedSubgroup (omegaMinusBetaC k b c) →* StatedSp 3 k :=
  (resMinus k (ne_zero_of_irreducible k hirr)).comp
    ((((StatedOmega (StatedQuadMinus 4 k b c)).subtype.comp
      (fixedSubgroup (omegaMinusBetaC k b c)).subtype)).codRestrict (minusStab k b c)
        fun A => coe_mem_minusStab k hirr A.2)

theorem coe_omegaMinusRes [Finite k] (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (A : fixedSubgroup (omegaMinusBetaC k b c)) :
    (((omegaMinusRes k hirr A : StatedSp 3 k) : GL (Fin 3 ⊕ Fin 3) k) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) =
      (((A : StatedOmega (StatedQuadMinus 4 k b c)) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix
          minusEmb minusEmb := rfl

variable [Finite k]

omit [CharP k 2] in
theorem omegaMinus_hconj {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card k = 2 ^ f)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ∀ α : MulAut (matrixProjectiveDerived (reindexQuadraticForm (minusIndexEquiv 4 (by norm_num))
      (quadMinus 4 k b c))), α * α = 1 → ∃ β, β⁻¹ * α * β ∈
        matrixProjectiveImage (reindexQuadraticForm (minusIndexEquiv 4 (by norm_num))
          (quadMinus 4 k b c)) := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus 4 k b c))) .POmegaMinus
      4 2 f :=
    ⟨⟨Nat.prime_two, hf, le_rfl⟩, k, inferInstance, inferInstance, hK, b, c, hirr,
      ⟨MulEquiv.refl _⟩⟩
  exact (even_orthogonal_involutions_conjugate_into_semilinear_image
    _ .POmegaMinus (Or.inr rfl) 4 f h).1 (by norm_num) k hK b c hirr (MulEquiv.refl _)

theorem exists_conj_omegaMinusBetaC {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (β : MulAut (StatedOmega (StatedQuadMinus 4 k b c)))
    (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉ (MulAut.conj : StatedOmega (StatedQuadMinus 4 k b c) ⧸
      center (StatedOmega (StatedQuadMinus 4 k b c)) →* MulAut _).range) {f' : ℕ}
    (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ Ψ : StatedOmega (StatedQuadMinus 4 k b c) ≃* StatedOmega (StatedQuadMinus 4 k b c),
      ∀ g, β (Ψ g) = Ψ (omegaMinusBetaC k b c g) :=
  exists_conj_omegaSymmetryAut hf hK le_rfl (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c)
    (coe_quadMinus 4 k b c) (regular_coordinateQuadMinus 4 k b c le_rfl hirr).1
    (regular_coordinateQuadMinus 4 k b c le_rfl hirr).2
    (commutator_coordinateQuadMinus 4 k b c le_rfl hirr) (omegaMinus_hconj k hf hK hirr)
    (matrixDerivedScalars_omegaMinus_eq_bot k b c) (quadMinus_minusVec k) β hβ2 hβo hfix

theorem nonempty_fixedSubgroup_omegaMinusBetaC_mulEquiv {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (fixedSubgroup (omegaMinusBetaC k b c) ≃* StatedSp 3 k) :=
  nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf hK le_rfl (minusIndexEquiv 4 (by norm_num))
    (quadMinus 4 k b c) (coe_quadMinus 4 k b c) (regular_coordinateQuadMinus 4 k b c le_rfl hirr).1
    (regular_coordinateQuadMinus 4 k b c le_rfl hirr).2
    (commutator_coordinateQuadMinus 4 k b c le_rfl hirr)
    (matrixDerivedScalars_omegaMinus_eq_bot k b c) (quadMinus_minusVec k)

omit [CharP k 2] [Finite k] in
theorem diagOmegaMinus_mulVec_minusVec (t : Fin 3 → kˣ) :
    (diagOmegaMinus k t : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ minusVec k = minusVec k := by
  rw [diagOmegaMinus_coe]
  funext i
  rw [mulVec_diagonal]
  rcases i with i | i | j
  · simp [minusVec]
  · simp [minusVec]
  · rw [minusWeight_inr_inr, one_mul]

theorem omegaMinusRes_injective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) : Function.Injective (omegaMinusRes k hirr) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨e⟩ := nonempty_fixedSubgroup_omegaMinusBetaC_mulEquiv k (by omega) hK hirr
  have : IsSimpleGroup (StatedSp 3 k) :=
    SymplecticPilot.isSimpleGroup_statedSp_of_four_le hk4 (by norm_num)
  have : IsSimpleGroup (fixedSubgroup (omegaMinusBetaC k b c)) := e.isSimpleGroup
  rcases (omegaMinusRes k hirr).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨a, ha⟩ := LieType.Steinberg.CentralExt.SpinTorus.exists_unit_sq_ne_one hk4
    set t : Fin 3 → kˣ := Pi.mulSingle 0 a with htdef
    have hfix : (⟨diagOmegaMinus k t, diagOmegaMinus_mem b c t⟩ :
        StatedOmega (StatedQuadMinus 4 k b c)) ∈ fixedSubgroup (omegaMinusBetaC k b c) := by
      rw [mem_fixedSubgroup_omegaMinusBetaC_iff k hirr]
      exact diagOmegaMinus_mulVec_minusVec k t
    have hker : (⟨_, hfix⟩ : fixedSubgroup (omegaMinusBetaC k b c)) ∈
        (omegaMinusRes k hirr).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hker
    have h1 := congrArg (fun A : StatedSp 3 k =>
      ((A : GL (Fin 3 ⊕ Fin 3) k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k)
        (Sum.inl 0) (Sum.inl 0)) hker
    simp only [coe_omegaMinusRes, submatrix_apply, diagOmegaMinus_coe, OneMemClass.coe_one,
      Units.val_one, one_apply_eq] at h1
    rw [diagonal_apply_eq, minusEmb, Sum.elim_inl, minusWeight_inl, htdef,
      Pi.mulSingle_eq_same] at h1
    apply ha
    rw [Units.val_eq_one.mp h1, one_pow]

theorem omegaMinusRes_bijective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) : Function.Bijective (omegaMinusRes k hirr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_omegaMinusBetaC_mulEquiv k (by omega) hK hirr
  exact (omegaMinusRes_injective k hK hf hirr).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

section Iota

variable {k} {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def omegaMinusIota :
    StatedSp 3 k →* StatedOmega (StatedQuadMinus 4 k b c) :=
  (fixedSubgroup (omegaMinusBetaC k b c)).subtype.comp
    (MulEquiv.ofBijective (omegaMinusRes k hirr)
      (omegaMinusRes_bijective k hK hf hirr)).symm.toMonoidHom

theorem omegaMinusIota_injective : Function.Injective (omegaMinusIota hK hf hirr) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_omegaMinusIota :
    (omegaMinusIota hK hf hirr).range = fixedSubgroup (omegaMinusBetaC k b c) := by
  rw [omegaMinusIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem omegaMinusIota_eq_of_res {g : StatedSp 3 k} {y : fixedSubgroup (omegaMinusBetaC k b c)}
    (hy : omegaMinusRes k hirr y = g) : omegaMinusIota hK hf hirr g = y := by
  change (((MulEquiv.ofBijective (omegaMinusRes k hirr)
    (omegaMinusRes_bijective k hK hf hirr)).symm g :
    fixedSubgroup (omegaMinusBetaC k b c)) : StatedOmega (StatedQuadMinus 4 k b c)) = y
  rw [(MulEquiv.symm_apply_eq _).mpr hy.symm]

theorem omegaMinusRes_omegaMinusIota (g : StatedSp 3 k) :
    omegaMinusRes k hirr ⟨omegaMinusIota hK hf hirr g,
      (range_omegaMinusIota hK hf hirr) ▸ ⟨g, rfl⟩⟩ = g :=
  MulEquiv.apply_symm_apply
    (MulEquiv.ofBijective (omegaMinusRes k hirr) (omegaMinusRes_bijective k hK hf hirr)) g

theorem coe_omegaMinusIota_sp6Diag (t : Fin 3 → kˣ) :
    ((omegaMinusIota hK hf hirr (sp6Diag k t) : StatedOmega (StatedQuadMinus 4 k b c)) :
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) = diagOmegaMinus k t := by
  have hfix : (⟨diagOmegaMinus k t, diagOmegaMinus_mem b c t⟩ :
      StatedOmega (StatedQuadMinus 4 k b c)) ∈ fixedSubgroup (omegaMinusBetaC k b c) := by
    rw [mem_fixedSubgroup_omegaMinusBetaC_iff k hirr]
    exact diagOmegaMinus_mulVec_minusVec k t
  rw [omegaMinusIota_eq_of_res hK hf hirr (y := ⟨_, hfix⟩)]
  apply mat_injective
  rw [mat_sp6Diag, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_omegaMinusRes]
  ext i j
  simp only [submatrix_apply, diagOmegaMinus_coe, diagonal_apply, minusEmb_injective.eq_iff]
  split_ifs with hij
  · subst hij
    rcases i with i | i
    · simp only [minusEmb, Sum.elim_inl, sp6Weight_inl]
      rfl
    · simp only [minusEmb, Sum.elim_inr, sp6Weight_inr]
      rfl
  · rfl

end Iota

end CFSG.SeitzReduction.F4Pilot
