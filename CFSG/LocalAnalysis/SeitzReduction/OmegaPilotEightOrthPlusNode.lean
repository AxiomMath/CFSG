module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFlip

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL mat_leviEmbedSL
  leviEmbedSL_injective)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.SeitzReduction.LinearPilot (blockEmbed blockMatrix blockMatrix_apply
  blockEmbed_injective range_blockEmbed reindexSpecialLinear)
open scoped MatrixGroups

section Param

variable {F : Type} [Field F] {m : ℕ}

variable (F) in
@[expose] noncomputable def siegelParam (B P : Finset (Fin m)) :
    SpecialLinearGroup B F →* GL (Fin m ⊕ Fin m) F :=
  (MulAut.conj (flipGL F P)).toMonoidHom.comp
    ((StatedSp m F).subtype.comp ((leviEmbedSL F m).comp (blockEmbed B)))

theorem siegelParam_injective (B P : Finset (Fin m)) :
    Function.Injective (siegelParam F B P) :=
  (MulAut.conj _).injective.comp ((StatedSp m F).subtype_injective.comp
    (leviEmbedSL_injective.comp (blockEmbed_injective B)))

theorem range_siegelParam (B P : Finset (Fin m)) :
    (siegelParam F B P).range =
      (siegelBlockGL F B).map (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [siegelParam, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    range_blockEmbed]
  rfl

theorem siegelParam_coe (B P : Finset (Fin m)) (A : SpecialLinearGroup B F) :
    ((siegelParam F B P A : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
      (flipPerm P).permMatrix F * fromBlocks (blockMatrix B A) 0 0
        (blockMatrix B ((A⁻¹ : SpecialLinearGroup B F) : Matrix B B F))ᵀ *
        (flipPerm P).permMatrix F := by
  change ((flipGL F P : GL (Fin m ⊕ Fin m) F) : Matrix _ _ F) *
      mat m F (leviEmbedSL F m (blockEmbed B A)) *
      (((flipGL F P)⁻¹ : GL (Fin m ⊕ Fin m) F) : Matrix _ _ F) = _
  rw [mat_leviEmbedSL, flipGL_inv, coe_flipGL, ← map_inv]
  rfl

theorem blockMatrix_map (B : Finset (Fin m)) (σ : F ≃+* F) (A : Matrix B B F) :
    (blockMatrix B A).map σ = blockMatrix B (A.map σ) := by
  ext i j
  rw [Matrix.map_apply, blockMatrix_apply, blockMatrix_apply]
  split_ifs with h
  · rfl
  · by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

theorem permMatrix_flipPerm_map (P : Finset (Fin m)) (σ : F ≃+* F) :
    ((flipPerm P).permMatrix F).map σ = (flipPerm P).permMatrix F := by
  ext i j
  rw [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem glCongr_siegelParam (B P : Finset (Fin m)) (σ : F ≃+* F) (A : SpecialLinearGroup B F) :
    glCongr σ (siegelParam F B P A) =
      siegelParam F B P (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  apply Units.ext
  rw [glCongr_coe, siegelParam_coe, siegelParam_coe, Matrix.map_mul, Matrix.map_mul,
    permMatrix_flipPerm_map, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ),
    Matrix.transpose_map, blockMatrix_map, blockMatrix_map, ← map_inv]
  rfl

end Param

section NodeParam

variable {F : Type} [Field F] {m : ℕ}

@[expose] noncomputable def finTwoEquiv {B : Finset (Fin m)} (hB : B.card = 2) : Fin 2 ≃ B :=
  (finCongr hB.symm).trans B.equivFin.symm

variable (F) in
@[expose] noncomputable def nodeParam (B P : Finset (Fin m)) (hB : B.card = 2) :
    SL(2, F) →* GL (Fin m ⊕ Fin m) F :=
  (siegelParam F B P).comp (reindexSpecialLinear (K := F) (finTwoEquiv hB)).toMonoidHom

theorem nodeParam_injective (B P : Finset (Fin m)) (hB : B.card = 2) :
    Function.Injective (nodeParam F B P hB) :=
  (siegelParam_injective B P).comp (reindexSpecialLinear (K := F) (finTwoEquiv hB)).injective

theorem range_nodeParam (B P : Finset (Fin m)) (hB : B.card = 2) :
    (nodeParam F B P hB).range =
      (siegelBlockGL F B).map (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [nodeParam, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
    (reindexSpecialLinear (K := F) (finTwoEquiv hB)).surjective, ← MonoidHom.range_eq_map,
    range_siegelParam]

theorem glCongr_nodeParam (B P : Finset (Fin m)) (hB : B.card = 2) (σ : F ≃+* F) (A : SL(2, F)) :
    glCongr σ (nodeParam F B P hB A) =
      nodeParam F B P hB (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  change glCongr σ (siegelParam F B P (reindexSpecialLinear (finTwoEquiv hB) A)) =
    siegelParam F B P (reindexSpecialLinear (finTwoEquiv hB)
      (Matrix.SpecialLinearGroup.map σ.toRingHom A))
  rw [glCongr_siegelParam]
  congr 1

theorem inv_apply_of_diag {A : SL(2, F)} (hA : ∀ i j : Fin 2, i ≠ j → (A : Matrix _ _ F) i j = 0) :
    ∀ i j : Fin 2, i ≠ j → ((A⁻¹ : SL(2, F)) : Matrix _ _ F) i j = 0 := by
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simp [hA 0 1 (by decide)]
  · simp [hA 1 0 (by decide)]
  · exact absurd rfl hij

theorem nodeParam_apply_ne_of_diag (B P : Finset (Fin m)) (hB : B.card = 2) {A : SL(2, F)}
    (hA : ∀ i j : Fin 2, i ≠ j → (A : Matrix _ _ F) i j = 0) {a b : Fin m ⊕ Fin m} (hab : a ≠ b) :
    ((nodeParam F B P hB A : GL (Fin m ⊕ Fin m) F) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = 0 := by
  have hAi := inv_apply_of_diag hA
  set e := finTwoEquiv hB with he
  have hR : ∀ (C : SL(2, F)), (∀ i j : Fin 2, i ≠ j → (C : Matrix _ _ F) i j = 0) →
      ∀ x y : Fin m, x ≠ y → blockMatrix B
        ((reindexSpecialLinear (K := F) e C : SpecialLinearGroup B F) : Matrix B B F) x y = 0 := by
    intro C hC x y hxy
    rw [blockMatrix_apply]
    split_ifs with h
    · change (C : Matrix _ _ F) (e.symm ⟨x, h.1⟩) (e.symm ⟨y, h.2⟩) = 0
      refine hC _ _ fun h' => hxy ?_
      have := congrArg Subtype.val (e.symm.injective h')
      exact this
    · exact Matrix.one_apply_ne hxy
  change ((siegelParam F B P (reindexSpecialLinear e A) : GL (Fin m ⊕ Fin m) F) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = 0
  rw [siegelParam_coe, permMatrix_conj_apply_eq, flipPerm_symm]
  have hne : flipPerm P a ≠ flipPerm P b := fun h => hab ((flipPerm P).injective h)
  rcases hfa : flipPerm P a with x | x <;> rcases hfb : flipPerm P b with y | y <;>
    rw [hfa, hfb] at hne
  · rw [fromBlocks_apply₁₁]
    exact hR A hA x y fun h => hne (by rw [h])
  · rw [fromBlocks_apply₁₂]; rfl
  · rw [fromBlocks_apply₂₁]; rfl
  · rw [fromBlocks_apply₂₂, transpose_apply, ← map_inv]
    exact hR A⁻¹ hAi y x fun h => hne (by rw [h])

theorem commute_diagOmega_of_apply_ne {X : GL (Fin m ⊕ Fin m) F}
    (hX : ∀ a b, a ≠ b → (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = 0)
    (u : Fin m → Fˣ) :
    X * diagOmega F m u = diagOmega F m u * X := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagOmega_coe]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : a = b
  · subst hab; exact mul_comm _ _
  · rw [hX a b hab, zero_mul, mul_zero]

end NodeParam

section Cover

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (commutator_centralizerPerfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {m : ℕ} {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)}
  {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F} {k : Fin (m + 1)}

omit [CharP F 2] in
theorem exists_nodeParam_of_cover (C : PlusFieldCover e ι k) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {σ : F ≃+* F}
    (hC3 : ∀ x : plusNeighbourCore e k, C.π ((plusNeighbourCore e k).normalizerMonoidHom ⟨t,
        UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _⟩ x) =
      statedOmegaPlusCongr σ m (C.π x))
    (hK : 4 ≤ Nat.card K) (hF5 : 5 ≤ Nat.card F) (hF9 : Nat.card F ≠ 9)
    {J : Finset (Fin (m + 1))} (P : Finset (Fin (m + 1))) (hk : k ∉ J) (hJ : J.card = 2) :
    ∃ φ : SL(2, F) ≃* plusSignedLevelCore e J P,
      (∀ A, ((C.π (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P) (φ A)) :
        StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
          nodeParam F (preimagePlanes k J) (preimagePlanes k P)
            ((card_preimagePlanes hk).trans hJ) A) ∧
      ∀ A, t * (φ A : G) * t⁻¹ = φ (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have hJ' : (preimagePlanes k J).card = 2 := (card_preimagePlanes hk).trans hJ
  set U := plusSignedLevelCore e J P with hU
  set E := plusNeighbourCore e k with hE
  have hUE : U ≤ E := plusSignedLevelCore_le_plusNeighbourCore e hk P
  have hM := C.map_signedLevelCore hK hF4 hk hJ.ge P
  set ρ := nodeParam F (preimagePlanes k J) (preimagePlanes k P) hJ' with hρ
  have hρi : Function.Injective ρ := nodeParam_injective _ _ hJ'
  set πU : U →* GL (Fin m ⊕ Fin m) F :=
    (StatedOmega (StatedQuadPlus m F)).subtype.comp (C.π.comp (Subgroup.inclusion hUE)) with hπU
  have hrange : πU.range = ρ.range := by
    rw [hπU, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range, hM, hρ,
      range_nodeParam]
  have hker : πU.ker ≤ center U := by
    intro u hu
    apply ker_comp_inclusion_le_center hUE C.π C.ker_le
    rw [MonoidHom.mem_ker] at hu ⊢
    exact Subtype.ext hu
  have : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_SL2_of_range_eq hF5 hF9 πU ρ hρi hrange hker
  have hπUi : Function.Injective πU := by
    intro u v huv
    rw [hΘ, hΘ] at huv
    exact Θ.injective (hρi huv)
  refine ⟨Θ.symm, fun A => ?_, fun A => ?_⟩
  · have h1 := hΘ (Θ.symm A)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  · have htU : t ∈ normalizer (U : Set G) :=
      UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
    have hmem : t * ((Θ.symm A : U) : G) * t⁻¹ ∈ U := (mem_normalizer_iff.1 htU _).1 (Θ.symm A).2
    have hval : πU ⟨_, hmem⟩ = πU (Θ.symm (Matrix.SpecialLinearGroup.map σ.toRingHom A)) := by
      have e1 : πU ⟨_, hmem⟩ = glCongr σ (πU (Θ.symm A)) := by
        change ((C.π (Subgroup.inclusion hUE ⟨_, hmem⟩) : StatedOmega (StatedQuadPlus m F)) :
          GL (Fin m ⊕ Fin m) F) = _
        rw [inclusion_conj_eq_normalizerMonoidHom hUE
          (UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _)
          (Θ.symm A) hmem, hC3]
        rfl
      rw [e1, hΘ, hΘ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hρ,
        glCongr_nodeParam]
    exact congrArg Subtype.val (hπUi hval)

end Cover

end CFSG.SeitzReduction.OmegaPilot
