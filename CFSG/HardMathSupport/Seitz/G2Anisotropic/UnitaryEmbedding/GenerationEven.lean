module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.StandardPair
public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley CFSG.Quasithin.G2U
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.SEITZ3

theorem rootTorusSL2_tuple {L : Type} [Field L] {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β)
    (c : Lˣ) :
    ∃ a : Fin Tag.G2.rank → Lˣ, rootTorusSL2 .G2 L β c = rootDiagUnit .G2 a ∧
      ∀ i, a i = c ^ (2 * iform β (Pi.single i 1) / iform β β) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport .G2 L hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  refine ⟨a, ha, fun i => ?_⟩
  have hγ : IsRoot .G2 (Pi.single i 1 : Fin Tag.G2.rank → ℤ) := isRoot_single .G2 i
  have h1 := (hv c).2 _ hγ
  rw [ha] at h1
  change rootDiag a (rootVec .G2 L (Pi.single i 1)) = _ at h1
  rw [rootDiag_rootVec a hγ] at h1
  have hne : rootVec .G2 L (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hγ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective L hne h1
  have h3 : rootChar a (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = a i := by
    rw [rootChar]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [← h3]
  exact Units.ext h2

section Weyl

theorem weyl_eq_one_of_basis (g : WeylGroup .G2) (h0 : g • (vec 1 0) = vec 1 0)
    (h1 : g • (vec 0 1) = vec 0 1) : g = 1 := by
  refine eq_of_smul_eq_smul (α := Fin Tag.G2.rank → ℤ) fun v => ?_
  have hv : v = (v ⟨0, by decide⟩) • vec 1 0 + (v ⟨1, by decide⟩) • vec 0 1 := by
    funext i
    fin_cases i
    · change v ⟨0, _⟩ = v ⟨0, _⟩ * 1 + v ⟨1, _⟩ * 0
      ring
    · change v ⟨1, _⟩ = v ⟨0, _⟩ * 0 + v ⟨1, _⟩ * 1
      ring
  rw [one_smul, hv]
  have key : ∀ (n : ℤ) (w : Fin Tag.G2.rank → ℤ), g • (n • w) = n • (g • w) := fun n w =>
    map_zsmul (AddMonoidHom.mk' (fun w : Fin Tag.G2.rank → ℤ => g • w) (smul_add g)) n w
  rw [smul_add, key, key, h0, h1]

@[expose] def rho (v : Fin Tag.G2.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  refl (vec 1 0) (refl (vec 1 3) v)

@[expose] def rho0 : WeylGroup .G2 := rootReflection (vec 1 0) * rootReflection (vec 1 3)

theorem rho0_smul (v : Fin Tag.G2.rank → ℤ) : rho0 • v = rho v := by
  have h0 : IsRoot .G2 (vec 1 0) := isRoot_of_mem_rootList (by decide)
  have h3 : IsRoot .G2 (vec 1 3) := isRoot_of_mem_rootList (by decide)
  rw [rho0, mul_smul, QPlusModel.rootReflection_smul_eq_refl ℚ h3,
    QPlusModel.rootReflection_smul_eq_refl ℚ h0]
  rfl

theorem rho0_pow_three : rho0 ^ 3 = 1 := by
  apply weyl_eq_one_of_basis
  · simp only [pow_succ, pow_zero, one_mul, mul_smul, rho0_smul]; decide
  · simp only [pow_succ, pow_zero, one_mul, mul_smul, rho0_smul]; decide

theorem rho0_ne_one : rho0 ≠ 1 := by
  intro h
  have := congrArg (fun g : WeylGroup .G2 => g • (vec 1 0)) h
  simp only [rho0_smul, one_smul] at this
  revert this; decide

theorem orderOf_rho0 : orderOf rho0 = 3 :=
  orderOf_eq_prime rho0_pow_three rho0_ne_one

end Weyl

section Model

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

abbrev QPlusModel.X (M : QPlusModel K σ) : Subgroup (ModGL .G2 K₂) :=
  ⨆ (γ : Fin Tag.G2.rank → ℤ) (_ : IsRoot .G2 γ), M.R γ

theorem QPlusModel.R_le_X (M : QPlusModel K σ) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) :
    M.R γ ≤ M.X :=
  le_iSup₂_of_le γ hγ le_rfl

theorem QPlusModel.X_le_gamma (M : QPlusModel K σ) : M.X ≤ M.gamma :=
  iSup₂_le fun _ _ => inf_le_right

abbrev QPlusModel.phi (M : QPlusModel K σ) : ModGL .G2 K →* ModGL .G2 K₂ :=
  (MulAut.conj M.g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))

theorem QPlusModel.phi_apply (M : QPlusModel K σ) (y : ModGL .G2 K) :
    M.phi y = M.g * baseChangeGL (algebraMap K K₂) y * M.g⁻¹ := rfl

theorem QPlusModel.phi_injective (M : QPlusModel K σ) : Function.Injective M.phi :=
  (MulAut.conj M.g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))

theorem QPlusModel.phi_mem_gamma (M : QPlusModel K σ) {y : ModGL .G2 K}
    (hy : y ∈ adjointGroup .G2 K) : M.phi y ∈ M.gamma :=
  Subgroup.mem_map_of_mem _ hy

theorem QPlusModel.phi_rootSL2_a (M : QPlusModel K σ) (A : SL2 K) :
    M.phi (rootSL2 .G2 K g2a A) ∈ rootRankOneGroup .G2 K₂ g2a := by
  rw [M.phi_apply, baseChangeGL_rootSL2_of_field, M.hgdef]
  set A' := Matrix.SpecialLinearGroup.map (algebraMap K K₂) A
  have hX : rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a A' =
      rootSL2 .G2 K₂ g2a A' * rootSL2 .G2 K₂ g2v M.P⁻¹ := rootSL2_g2v_mul_rootSL2_g2a _ _
  have h1 : rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a A' * (rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a A' := by rw [hX, mul_inv_cancel_right]
  have h2 : rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a A' *
      (rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a M.P⁻¹ * (rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a A' *
        (rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹) * (rootSL2 .G2 K₂ g2a M.P⁻¹)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [h2, h1]
  exact ⟨M.P⁻¹ * A' * M.P⁻¹⁻¹, by simp [map_mul, map_inv]⟩

theorem QPlusModel.phi_rootSL2_v (M : QPlusModel K σ) (B : SL2 K) :
    M.phi (rootSL2 .G2 K g2v B) ∈ rootRankOneGroup .G2 K₂ g2v := by
  rw [M.phi_apply, baseChangeGL_rootSL2_of_field, M.hgdef]
  set B' := Matrix.SpecialLinearGroup.map (algebraMap K K₂) B
  have hY : ∀ C : SL2 K₂, rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v C *
      (rootSL2 .G2 K₂ g2a M.P⁻¹)⁻¹ = rootSL2 .G2 K₂ g2v C := fun C => by
    rw [← rootSL2_g2v_mul_rootSL2_g2a C M.P⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2v B' *
      (rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a M.P⁻¹ * (rootSL2 .G2 K₂ g2v (M.P⁻¹ * B' * M.P⁻¹⁻¹)) *
        (rootSL2 .G2 K₂ g2a M.P⁻¹)⁻¹ := by
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
  rw [h2, hY]
  exact ⟨_, rfl⟩

theorem QPlusModel.stdA1A1_le_comap (M : QPlusModel K σ) :
    stdA1A1 K ≤ M.X.comap (M.phi.comp (adjointGroup .G2 K).subtype) := by
  have ha0 : IsRoot .G2 g2a := isRoot_of_mem_rootList (by decide)
  have hv0 : IsRoot .G2 g2v := isRoot_of_mem_rootList (by decide)
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K),
      rootSL2 .G2 K β A ∈ adjointGroup .G2 K :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K β).2.2.2.2.1 A
  rintro _ ⟨⟨A, B⟩, rfl⟩
  show M.phi ((a1a1Hom K (A, B) : adjointGroup .G2 K) : ModGL .G2 K) ∈ M.X
  rw [a1a1Hom_apply, map_mul]
  exact M.X.mul_mem
    (M.R_le_X ha0 ⟨M.phi_rootSL2_a A, M.phi_mem_gamma (hρC _ A)⟩)
    (M.R_le_X hv0 ⟨M.phi_rootSL2_v B, M.phi_mem_gamma (hρC _ B)⟩)

end Model

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
