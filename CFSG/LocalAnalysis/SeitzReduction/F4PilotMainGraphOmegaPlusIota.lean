module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTablesSp6
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  commutator_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.SeitzReduction.OmegaPilot (diagOmega isometryClosure isometry_of_mem_isometryClosure
  diagOmega_coe)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_involutions_conjugate_into_semilinear_image)

variable (k : Type) [Field k]

theorem quadPlus_omegaPlusVec : quadPlus 4 k (omegaPlusVec k) = 1 := by
  rw [coe_quadPlus]
  exact statedQuadPlus_omegaPlusVec k

theorem reindexQuadraticForm_plus_omegaPlusVec :
    reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k)
      (reindexVectorEquiv (plusIndexEquiv 4) (omegaPlusVec k)) = 1 := by
  rw [reindexQuadraticForm_reindexVectorEquiv, quadPlus_omegaPlusVec]

variable [CharP k 2]

theorem matrixDerivedScalars_omegaPlus_eq_bot :
    matrixDerivedScalars (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k)) = ⊥ :=
  LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo _
    ⟨_, by rw [reindexQuadraticForm_plus_omegaPlusVec]; exact one_ne_zero⟩

@[expose] noncomputable def omegaPlusBetaC : MulAut (StatedOmega (StatedQuadPlus 4 k)) :=
  omegaSymmetryAut (plusIndexEquiv 4) (quadPlus 4 k) (coe_quadPlus 4 k)
    (matrixDerivedScalars_omegaPlus_eq_bot k) (omegaPlusVec k)

theorem mem_fixedSubgroup_omegaPlusBetaC_iff (A : StatedOmega (StatedQuadPlus 4 k)) :
    A ∈ fixedSubgroup (omegaPlusBetaC k) ↔
      ((A : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ omegaPlusVec k =
        omegaPlusVec k :=
  mem_fixedSubgroup_omegaSymmetryAut_iff _ _ _ _ _
    (regular_coordinateQuadPlus 4 k (by norm_num)).1 (quadPlus_omegaPlusVec k) A

omit [CharP k 2] in
theorem isometry_of_mem_omegaPlus8 (A : StatedOmega (StatedQuadPlus 4 k))
    (x : Fin 4 ⊕ Fin 4 → k) :
    StatedQuadPlus 4 k
      (((A : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ x) =
        StatedQuadPlus 4 k x :=
  isometry_of_mem_isometryClosure (Subgroup.commutator_le_self _ A.2) x

theorem coe_mem_plusStab {A : StatedOmega (StatedQuadPlus 4 k)}
    (hA : A ∈ fixedSubgroup (omegaPlusBetaC k)) : (A : GL (Fin 4 ⊕ Fin 4) k) ∈ plusStab k :=
  ⟨isometry_of_mem_omegaPlus8 k A, (mem_fixedSubgroup_omegaPlusBetaC_iff k A).1 hA⟩

@[expose] noncomputable def omegaPlusRes : fixedSubgroup (omegaPlusBetaC k) →* StatedSp 3 k :=
  (resPlus k).comp ((((StatedOmega (StatedQuadPlus 4 k)).subtype.comp
    (fixedSubgroup (omegaPlusBetaC k)).subtype)).codRestrict (plusStab k)
      fun A => coe_mem_plusStab k A.2)

theorem coe_omegaPlusRes (A : fixedSubgroup (omegaPlusBetaC k)) :
    (((omegaPlusRes k A : StatedSp 3 k) : GL (Fin 3 ⊕ Fin 3) k) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) =
      (((A : StatedOmega (StatedQuadPlus 4 k)) : GL (Fin 4 ⊕ Fin 4) k) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).submatrix plusEmb plusEmb := rfl

variable [Finite k]

omit [CharP k 2] in
theorem omegaPlus_hconj {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card k = 2 ^ f) :
    ∀ α : MulAut (matrixProjectiveDerived (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k))),
      α * α = 1 → ∃ β, β⁻¹ * α * β ∈
        matrixProjectiveImage (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k)) := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 k))) .POmegaPlus 4 2 f :=
    ⟨⟨Nat.prime_two, hf, le_rfl⟩, k, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  exact ((even_orthogonal_involutions_conjugate_into_semilinear_image
    _ .POmegaPlus (Or.inl rfl) 4 f h).1 k hK (MulEquiv.refl _)).1

theorem exists_conj_omegaPlusBetaC {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) (β : MulAut (StatedOmega (StatedQuadPlus 4 k)))
    (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉ (MulAut.conj : StatedOmega (StatedQuadPlus 4 k) ⧸
      center (StatedOmega (StatedQuadPlus 4 k)) →* MulAut _).range) {f' : ℕ}
    (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ Ψ : StatedOmega (StatedQuadPlus 4 k) ≃* StatedOmega (StatedQuadPlus 4 k),
      ∀ g, β (Ψ g) = Ψ (omegaPlusBetaC k g) :=
  exists_conj_omegaSymmetryAut hf hK le_rfl (plusIndexEquiv 4) (quadPlus 4 k) (coe_quadPlus 4 k)
    (regular_coordinateQuadPlus 4 k (by norm_num)).1
    (regular_coordinateQuadPlus 4 k (by norm_num)).2
    (commutator_coordinateQuadPlus 4 k (by norm_num)) (omegaPlus_hconj k hf hK)
    (matrixDerivedScalars_omegaPlus_eq_bot k) (quadPlus_omegaPlusVec k) β hβ2 hβo hfix

theorem nonempty_fixedSubgroup_omegaPlusBetaC_mulEquiv {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) : Nonempty (fixedSubgroup (omegaPlusBetaC k) ≃* StatedSp 3 k) :=
  nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf hK le_rfl (plusIndexEquiv 4) (quadPlus 4 k)
    (coe_quadPlus 4 k) (regular_coordinateQuadPlus 4 k (by norm_num)).1
    (regular_coordinateQuadPlus 4 k (by norm_num)).2
    (commutator_coordinateQuadPlus 4 k (by norm_num))
    (matrixDerivedScalars_omegaPlus_eq_bot k) (quadPlus_omegaPlusVec k)

omit [CharP k 2] [Finite k] in
theorem diagOmega_mulVec_omegaPlusVec {t : Fin 4 → kˣ} (ht : t 3 = 1) :
    (diagOmega k 4 t : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ omegaPlusVec k =
      omegaPlusVec k := by
  rw [diagOmega_coe]
  funext i
  rw [mulVec_diagonal]
  rcases i with i | i
  · rw [omegaPlusVec_inl]
    by_cases hi : i = 3
    · subst hi
      simp [ht]
    · simp [hi]
  · rw [omegaPlusVec_inr]
    by_cases hi : i = 3
    · subst hi
      simp [ht]
    · simp [hi]

theorem omegaPlusRes_injective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k)) :
    Function.Injective (omegaPlusRes k) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨e⟩ := nonempty_fixedSubgroup_omegaPlusBetaC_mulEquiv k (by omega) hK
  have : IsSimpleGroup (StatedSp 3 k) :=
    SymplecticPilot.isSimpleGroup_statedSp_of_four_le hk4 (by norm_num)
  have : IsSimpleGroup (fixedSubgroup (omegaPlusBetaC k)) := e.isSimpleGroup
  rcases (omegaPlusRes k).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨a, ha⟩ := LieType.Steinberg.CentralExt.SpinTorus.exists_unit_sq_ne_one hk4
    set t : Fin 4 → kˣ := Pi.mulSingle 0 a with htdef
    have hfix : (⟨diagOmega k 4 t, hdiag t⟩ : StatedOmega (StatedQuadPlus 4 k)) ∈
        fixedSubgroup (omegaPlusBetaC k) := by
      rw [mem_fixedSubgroup_omegaPlusBetaC_iff]
      exact diagOmega_mulVec_omegaPlusVec k (by rw [htdef, Pi.mulSingle_eq_of_ne (by decide)])
    have hker : (⟨_, hfix⟩ : fixedSubgroup (omegaPlusBetaC k)) ∈ (omegaPlusRes k).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hker
    have h1 := congrArg (fun A : StatedSp 3 k =>
      ((A : GL (Fin 3 ⊕ Fin 3) k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k)
        (Sum.inl 0) (Sum.inl 0)) hker
    simp only [coe_omegaPlusRes, submatrix_apply, diagOmega_coe, OneMemClass.coe_one,
      Units.val_one, one_apply_eq] at h1
    rw [diagonal_apply_eq, plusEmb, Sum.map_inl, SymplecticPilot.diagSpEntry_inl, htdef] at h1
    have h2 : (Fin.castSucc (0 : Fin 3) : Fin 4) = 0 := rfl
    rw [h2, Pi.mulSingle_eq_same] at h1
    apply ha
    rw [Units.val_eq_one.mp h1, one_pow]

theorem omegaPlusRes_bijective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k)) :
    Function.Bijective (omegaPlusRes k) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_omegaPlusBetaC_mulEquiv k (by omega) hK
  exact (omegaPlusRes_injective k hK hf hdiag).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

@[expose] def snocOne (t : Fin 3 → kˣ) : Fin 4 → kˣ := Fin.snoc (α := fun _ => kˣ) t 1

omit [CharP k 2] [Finite k] in
@[simp] theorem snocOne_castSucc (t : Fin 3 → kˣ) (i : Fin 3) :
    snocOne k t (Fin.castSucc i) = t i := Fin.snoc_castSucc (α := fun _ => kˣ) _ _ _

omit [CharP k 2] [Finite k] in
@[simp] theorem snocOne_three (t : Fin 3 → kˣ) : snocOne k t 3 = 1 :=
  Fin.snoc_last (α := fun _ => kˣ) _ _

section Iota

variable {k} {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
  (hdiag : ∀ t : Fin 4 → kˣ, diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k))

@[expose] noncomputable def omegaPlusIota : StatedSp 3 k →* StatedOmega (StatedQuadPlus 4 k) :=
  (fixedSubgroup (omegaPlusBetaC k)).subtype.comp
    (MulEquiv.ofBijective (omegaPlusRes k) (omegaPlusRes_bijective k hK hf hdiag)).symm.toMonoidHom

theorem omegaPlusIota_injective : Function.Injective (omegaPlusIota hK hf hdiag) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_omegaPlusIota :
    (omegaPlusIota hK hf hdiag).range = fixedSubgroup (omegaPlusBetaC k) := by
  rw [omegaPlusIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem omegaPlusIota_eq_of_res {g : StatedSp 3 k} {y : fixedSubgroup (omegaPlusBetaC k)}
    (hy : omegaPlusRes k y = g) : omegaPlusIota hK hf hdiag g = y := by
  change (((MulEquiv.ofBijective (omegaPlusRes k) (omegaPlusRes_bijective k hK hf hdiag)).symm g :
    fixedSubgroup (omegaPlusBetaC k)) : StatedOmega (StatedQuadPlus 4 k)) = y
  rw [(MulEquiv.symm_apply_eq _).mpr hy.symm]

theorem coe_omegaPlusIota_sp6Diag (t : Fin 3 → kˣ) :
    ((omegaPlusIota hK hf hdiag (sp6Diag k t) : StatedOmega (StatedQuadPlus 4 k)) :
      GL (Fin 4 ⊕ Fin 4) k) = diagOmega k 4 (snocOne k t) := by
  have hfix : (⟨diagOmega k 4 (snocOne k t), hdiag _⟩ : StatedOmega (StatedQuadPlus 4 k)) ∈
      fixedSubgroup (omegaPlusBetaC k) := by
    rw [mem_fixedSubgroup_omegaPlusBetaC_iff]
    exact diagOmega_mulVec_omegaPlusVec k (snocOne_three k t)
  rw [omegaPlusIota_eq_of_res hK hf hdiag (y := ⟨_, hfix⟩)]
  apply mat_injective
  rw [mat_sp6Diag, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_omegaPlusRes]
  ext i j
  simp only [submatrix_apply, diagOmega_coe, diagonal_apply, plusEmb_injective.eq_iff]
  split_ifs with hij
  · subst hij
    rcases i with i | i
    · simp [plusEmb]
    · simp [plusEmb]
  · rfl

theorem omegaPlusRes_omegaPlusIota (g : StatedSp 3 k) :
    omegaPlusRes k ⟨omegaPlusIota hK hf hdiag g,
      (range_omegaPlusIota hK hf hdiag) ▸ ⟨g, rfl⟩⟩ = g := by
  have h := MulEquiv.apply_symm_apply
    (MulEquiv.ofBijective (omegaPlusRes k) (omegaPlusRes_bijective k hK hf hdiag)) g
  exact h

end Iota

end CFSG.SeitzReduction.F4Pilot
