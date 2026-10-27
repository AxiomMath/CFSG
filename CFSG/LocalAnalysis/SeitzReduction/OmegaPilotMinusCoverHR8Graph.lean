module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Main
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndFieldAut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo
  symmetryIsometry symmetryAut kappa_derived_eq_conj)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (evenOrthogonalRealization_of_regular)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair fieldAutT_mk
  matrixDerivedConjugation_fieldPair_val)
open CFSG.RankThree.PartOne.KCOrthogonalDescent (matrixProjectiveSimilarityEquiv
  matrixProjectiveSimilarityEquiv_mk exists_conj_mem_matrixDerived)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)

section Root

theorem exists_root_frob_of_irreducible {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : orderOf σ = 2) {β γ : F} (hβ : σ β = β) (hγ : σ γ = γ)
    (hirr : ∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0) :
    ∃ α : F, α ^ 2 + β * α + γ = 0 ∧ σ α = -β - α ∧ β ≠ 0 := by
  set k₀ : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F) with hk₀
  have hmem : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have : CharP k₀ 2 := RingHom.charP k₀.subtype Subtype.val_injective 2
  obtain ⟨f, -, hk⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k₀)
  have hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range k₀.subtype := fun x => by
    rw [← hmem]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hF := SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix k₀.subtype hk hσ hfix
  have hFK : Nat.card F = Nat.card k₀ ^ 2 := by rw [hF, hk, ← pow_mul, mul_comm]
  have hirr₀ : ∀ s : k₀, s ^ 2 + ⟨β, (hmem β).2 hβ⟩ * s + ⟨γ, (hmem γ).2 hγ⟩ ≠ 0 := by
    intro s hs
    apply hirr s ((hmem s).1 s.2)
    have h1 := congrArg (fun x : k₀ => (x : F)) hs
    simpa using h1
  obtain ⟨α, hα⟩ := exists_root_of_card_eq_sq k₀.subtype hFK hirr₀
  change α ^ 2 + β * α + γ = 0 at hα
  have hβ0 : β ≠ 0 := by
    intro h0
    apply coeff_ne_zero_of_irreducible hirr₀
    exact Subtype.ext h0
  have hσroot : σ α ^ 2 + β * σ α + γ = 0 := by
    rw [← hβ, ← hγ, ← map_pow, ← map_mul, ← map_add, ← map_add, hα, map_zero]
  have hne : σ α ≠ α := fun h => hirr α h hα
  have hprod : (σ α - α) * (σ α - (-β - α)) = 0 := by linear_combination hσroot - hα
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact ⟨α, hα, sub_eq_zero.1 h, hβ0⟩

end Root

section LastPlane

variable {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def lastPlaneVec (r : ℕ) : Fin (2 * (r + 1)) → F :=
  Pi.single (plusIndexEquiv (r + 1) (.inl (Fin.last r))) 1 +
    Pi.single (plusIndexEquiv (r + 1) (.inr (Fin.last r))) 1

theorem coordinateQuadPlus_lastPlaneVec : coordinateQuadPlus (r + 1) F (lastPlaneVec r) = 1 := by
  have h := (isHypCoord_coordinateQuadPlus (K := F) (Fin.last r)).map_add_smul 1 1
    (p := 0) rfl rfl
  simpa [lastPlaneVec] using h

theorem polar_lastPlaneVec (u : Fin (2 * (r + 1)) → F) :
    polar (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) u =
      u (plusIndexEquiv (r + 1) (.inr (Fin.last r))) +
        u (plusIndexEquiv (r + 1) (.inl (Fin.last r))) := by
  rw [lastPlaneVec, polar_add_left,
    (isHypCoord_coordinateQuadPlus (K := F) (Fin.last r)).polar_left,
    (isHypCoord_coordinateQuadPlus (K := F) (Fin.last r)).polar_right]

theorem lastPlaneVec_inl_last :
    lastPlaneVec (F := F) r (plusIndexEquiv (r + 1) (.inl (Fin.last r))) = 1 := by
  simp [lastPlaneVec, (plusIndexEquiv (r + 1)).injective.eq_iff]

theorem lastPlaneVec_inr_last :
    lastPlaneVec (F := F) r (plusIndexEquiv (r + 1) (.inr (Fin.last r))) = 1 := by
  simp [lastPlaneVec, (plusIndexEquiv (r + 1)).injective.eq_iff]

theorem lastPlaneVec_inl_castSucc (l : Fin r) :
    lastPlaneVec (F := F) r (plusIndexEquiv (r + 1) (.inl l.castSucc)) = 0 := by
  simp [lastPlaneVec, (plusIndexEquiv (r + 1)).injective.eq_iff, Fin.castSucc_ne_last]

theorem lastPlaneVec_inr_castSucc (l : Fin r) :
    lastPlaneVec (F := F) r (plusIndexEquiv (r + 1) (.inr l.castSucc)) = 0 := by
  simp [lastPlaneVec, (plusIndexEquiv (r + 1)).injective.eq_iff, Fin.castSucc_ne_last]

theorem symmetryGL_lastPlaneVec_mulVec [CharP F 2] (u : Fin (2 * (r + 1)) → F) :
    (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) :
        Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) F) *ᵥ u =
      u + (u (plusIndexEquiv (r + 1) (.inr (Fin.last r))) +
        u (plusIndexEquiv (r + 1) (.inl (Fin.last r)))) • lastPlaneVec r := by
  rw [symmetryGL_mulVec_of_charTwo coordinateQuadPlus_lastPlaneVec, polar_lastPlaneVec]

end LastPlane

section Mat

variable {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def minusPlusMat (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) : GL (Fin (2 * (r + 1))) F :=
  matrixLinearIso.symm (minusPlusIsometry hn hα hαα).toLinearEquiv

theorem minusPlusMat_mulVec (hn : 1 ≤ r + 1) {α β γ : F} (hα : α ^ 2 + β * α + γ = 0)
    (hαα : α ≠ -β - α) (v : Fin (2 * (r + 1)) → F) :
    (minusPlusMat hn hα hαα : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) F) *ᵥ v =
      minusPlusLin hn α (-β - α) v := by
  change matrixLinearIso (minusPlusMat hn hα hαα) v = _
  rw [minusPlusMat, MulEquiv.apply_symm_apply]
  rfl

theorem minusPlusMat_isometry (hn : 1 ≤ r + 1) {α β γ : F} (hα : α ^ 2 + β * α + γ = 0)
    (hαα : α ≠ -β - α) (v : Fin (2 * (r + 1)) → F) :
    coordinateQuadPlus (r + 1) F (matrixLinearIso (minusPlusMat hn hα hαα) v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus (r + 1) F hn β γ v := by
  rw [Units.val_one, one_mul, minusPlusMat, MulEquiv.apply_symm_apply]
  exact (minusPlusIsometry hn hα hαα).map_app v

variable [CharP F 2]

theorem symmetryGL_mul_glFieldAut_minusPlusMat (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) {σ : F ≃+* F} (hσα : σ α = -β - α)
    (hσβ : σ β = β) :
    symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) *
        glFieldAut (Fin (2 * (r + 1))) F σ (minusPlusMat hn hα hαα) =
      minusPlusMat hn hα hαα := by
  have hσα' : σ (-β - α) = α := by rw [map_sub, map_neg, hσβ, hσα]; ring
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ w : Fin (2 * (r + 1)) → F,
      ((symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) *
          glFieldAut (Fin (2 * (r + 1))) F σ (minusPlusMat hn hα hαα) : GL _ F) :
        Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) F) *ᵥ w =
      (minusPlusMat hn hα hαα : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) F) *ᵥ w := by
    intro w
    obtain ⟨w', rfl⟩ := (coordinateFieldMap (2 * (r + 1)) σ).surjective w
    have h1 := coordinateFieldMap_matrix σ (minusPlusMat hn hα hαα) w'
    rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h1, minusPlusMat_mulVec, minusPlusMat_mulVec,
      symmetryGL_lastPlaneVec_mulVec]
    funext j
    obtain ⟨τ, rfl⟩ := (plusIndexEquiv (r + 1)).surjective j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateFieldMap_apply]
    rcases τ with p | p
    · induction p using Fin.lastCases with
      | last =>
        simp only [lastPlaneVec_inl_last, minusPlusLin_inl_last, minusPlusLin_inr_last,
          coordinateFieldMap_apply, map_sub, map_mul, hσα, hσα', mul_one]
        linear_combination (σ (w' (minusIndexEquiv (r + 1) hn (.inr (.inr 0)))) -
          (-β - α) * σ (w' (minusIndexEquiv (r + 1) hn (.inr (.inr 1))))) * h2
      | cast l =>
        simp only [lastPlaneVec_inl_castSucc, minusPlusLin_inl_castSucc,
          coordinateFieldMap_apply, mul_zero, add_zero]
    · induction p using Fin.lastCases with
      | last =>
        simp only [lastPlaneVec_inr_last, minusPlusLin_inl_last, minusPlusLin_inr_last,
          coordinateFieldMap_apply, map_sub, map_mul, hσα, hσα', mul_one]
        linear_combination (σ (w' (minusIndexEquiv (r + 1) hn (.inr (.inr 0)))) -
          α * σ (w' (minusIndexEquiv (r + 1) hn (.inr (.inr 1))))) * h2
      | cast l =>
        simp only [lastPlaneVec_inr_castSucc, minusPlusLin_inr_castSucc,
          coordinateFieldMap_apply, mul_zero, add_zero]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h

end Mat

section Sim

variable {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ}

@[expose] noncomputable def minusPlusSim (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) :
    matrixProjectiveDerived (coordinateQuadMinus (r + 1) F hn β γ) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (r + 1) F) :=
  matrixProjectiveSimilarityEquiv _ _ (minusPlusMat hn hα hαα) 1 (minusPlusMat_isometry hn hα hαα)

omit [Finite F] [CharP F 2] in
private theorem conj_eq_of_mul_eq {M : Type*} [Group M] {a b c s : M} (h : s * b = a) :
    a * c * a⁻¹ = s * (b * c * b⁻¹) * s⁻¹ := by
  rw [← h]
  group

theorem congr_minusPlusSim_fieldAutT (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) {σ : F ≃+* F} (hσα : σ α = -β - α)
    (hβ : σ β = β) (hγ : σ γ = γ) :
    MulAut.congr (minusPlusSim hn hα hαα)
        (fieldAutT (coordinateQuadMinus (r + 1) F hn β γ) σ
          (coordinateQuadMinus_fieldMap_of_fixed hn hβ hγ)) =
      symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) * fieldAutHom F (r + 1) σ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (minusPlusSim hn hα hαα).surjective x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective _ y
  change minusPlusSim hn hα hαα (fieldAutT _ σ _ ((minusPlusSim hn hα hαα).symm
      (minusPlusSim hn hα hαα (matrixProjectiveProjection _ A)))) =
    symmetryAut _ _ (fieldAutHom F (r + 1) σ
      (minusPlusSim hn hα hαα (matrixProjectiveProjection _ A)))
  rw [MulEquiv.symm_apply_apply]
  obtain ⟨A₁, hA₁⟩ := exists_conj_mem_matrixDerived _ _ (minusPlusMat hn hα hαα) 1
    (minusPlusMat_isometry hn hα hαα) A
  have hBA : minusPlusSim hn hα hαα (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ A₁ :=
    matrixProjectiveSimilarityEquiv_mk _ _ _ _ _ A A₁ hA₁
  rw [hBA, fieldAutT_mk]
  obtain ⟨A₂, hA₂⟩ := exists_conj_mem_matrixDerived _ _ (minusPlusMat hn hα hαα) 1
    (minusPlusMat_isometry hn hα hαα)
    (matrixDerivedConjugation _ (fieldPair _ σ (coordinateQuadMinus_fieldMap_of_fixed hn hβ hγ)) A)
  rw [show minusPlusSim hn hα hαα = matrixProjectiveSimilarityEquiv _ _ (minusPlusMat hn hα hαα) 1
      (minusPlusMat_isometry hn hα hαα) from rfl,
    matrixProjectiveSimilarityEquiv_mk _ _ _ _ _ _ A₂ hA₂, fieldAutHom_apply, fieldAutT_mk]
  change _ = matrixProjectiveConjugation _ _ (matrixProjectiveProjection _ _)
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [hA₂, matrixDerivedConjugation_fieldPair_val, matrixDerivedConjugation_val,
    matrixDerivedConjugation_fieldPair_val, hA₁, matrixIsometryInclusion_val]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply,
    map_mul, map_inv]
  exact conj_eq_of_mul_eq (symmetryGL_mul_glFieldAut_minusPlusMat hn hα hαα hσα hβ)

end Sim

section InnField

theorem omegaMinus_mulAut_mul_conj {X : Type*} [Group X] (α : MulAut X) (x : X) :
    α * MulAut.conj x = MulAut.conj (α x) * α := by
  apply MulEquiv.ext
  intro y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem omegaMinus_mulAut_congr_conj {X Y : Type*} [Group X] [Group Y] (B : X ≃* Y) (x : X) :
    MulAut.congr B (MulAut.conj x) = MulAut.conj (B x) := by
  apply MulEquiv.ext
  intro y
  change B (x * B.symm y * x⁻¹) = B x * y * (B x)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

variable (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ)

@[expose] noncomputable def innFieldSubgroup :
    Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))) where
  carrier := {α | ∃ x, ∃ c : F ≃+* F, α = MulAut.conj x * fieldAutHom F n c}
  one_mem' := ⟨1, 1, by rw [map_one, map_one, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨x, c, rfl⟩ ⟨x', c', rfl⟩
    refine ⟨x * fieldAutHom F n c x', c * c', ?_⟩
    rw [map_mul MulAut.conj, map_mul (fieldAutHom F n)]
    calc MulAut.conj x * fieldAutHom F n c * (MulAut.conj x' * fieldAutHom F n c')
        = MulAut.conj x * (fieldAutHom F n c * MulAut.conj x') * fieldAutHom F n c' := by group
      _ = MulAut.conj x * (MulAut.conj (fieldAutHom F n c x') * fieldAutHom F n c) *
          fieldAutHom F n c' := by rw [omegaMinus_mulAut_mul_conj]
      _ = _ := by group
  inv_mem' := by
    rintro _ ⟨x, c, rfl⟩
    refine ⟨fieldAutHom F n c⁻¹ x⁻¹, c⁻¹, ?_⟩
    calc (MulAut.conj x * fieldAutHom F n c)⁻¹
        = fieldAutHom F n c⁻¹ * MulAut.conj x⁻¹ := by
          rw [_root_.mul_inv_rev, map_inv (fieldAutHom F n), map_inv MulAut.conj]
      _ = _ := by rw [omegaMinus_mulAut_mul_conj]

variable {F n}

theorem mem_innFieldSubgroup {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} :
    α ∈ innFieldSubgroup F n ↔ ∃ x, ∃ c : F ≃+* F, α = MulAut.conj x * fieldAutHom F n c :=
  Iff.rfl

theorem symmetryAut_mul_fieldAutHom_not_mem {r : ℕ} (hr : 4 ≤ r) (σ : F ≃+* F) :
    symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) * fieldAutHom F (r + 1) σ ∉
      innFieldSubgroup F (r + 1) := by
  intro hmem
  obtain ⟨x, c, h⟩ := mem_innFieldSubgroup.1 hmem
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (r + 1) F (by omega)
  have hE := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.commutator_coordinateQuadPlus
    (K := F) (n := r + 1) (by omega)
  obtain ⟨-, -, -, -, Fm, hFm, -, -, -⟩ :=
    evenOrthogonalRealization_of_regular hg hFc (by omega : 1 ≤ 2 * (r + 1)) _ hQ hT hE
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus F (r + 1)
    (by omega)
  have hmemI : ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus (r + 1) F)),
      α ∈ matrixProjectiveImage (coordinateQuadPlus (r + 1) F) := fun α => by
    rw [htop]
    exact mem_top α
  set Φ := Fm.comp ((MonoidHom.id _).codRestrict _ hmemI) with hΦ
  have hΦκ : ∀ S : similarityPairs (coordinateQuadPlus (r + 1) F),
      Φ (matrixProjectiveConjugationHom _ S) = S.val.right := fun S => hFm S
  have hx : Φ (MulAut.conj x) = 1 := by
    obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
    rw [← kappa_derived_eq_conj, hΦκ]
    rfl
  have hs : Φ (symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)) = 1 := hΦκ _
  have hσ' : Φ (fieldAutHom F (r + 1) σ) = σ := hΦκ _
  have hc : Φ (fieldAutHom F (r + 1) c) = c := hΦκ _
  have h1 := congrArg Φ h
  rw [map_mul, map_mul, hx, hs, hσ', hc, one_mul, one_mul] at h1
  subst h1
  have h2 : symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) = MulAut.conj x :=
    mul_right_cancel h
  exact F4Pilot.symmetryAut_not_mem_inner_of_regular hQ hT hE coordinateQuadPlus_lastPlaneVec
    ⟨x, h2.symm⟩

theorem index_innFieldSubgroup {r : ℕ} (hr : 4 ≤ r) : (innFieldSubgroup F (r + 1)).index = 2 := by
  obtain ⟨-, γ', -, -, hγ2, -, hγs, hform⟩ := omegaPlusAutNormalFormInput_holds F (r + 1) (by omega)
  have hconj : ∀ g, MulAut.conj g ∈ innFieldSubgroup F (r + 1) := fun g =>
    mem_innFieldSubgroup.2 ⟨g, 1, by rw [map_one, mul_one]⟩
  have hfld : ∀ c, fieldAutHom F (r + 1) c ∈ innFieldSubgroup F (r + 1) := fun c =>
    mem_innFieldSubgroup.2 ⟨1, c, by rw [map_one, one_mul]⟩
  have hγ : γ' ∉ innFieldSubgroup F (r + 1) := by
    intro hγ
    apply symmetryAut_mul_fieldAutHom_not_mem hr (1 : F ≃+* F)
    obtain ⟨g, c, h | h⟩ := hform (symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r) *
      fieldAutHom F (r + 1) 1)
    · rw [h]
      exact mul_mem (hconj g) (hfld c)
    · rw [h]
      exact mul_mem (mul_mem (hconj g) hγ) (hfld c)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨γ', fun b => ?_⟩
  obtain ⟨g, c, h | h⟩ := hform b
  · have hb : b ∈ innFieldSubgroup F (r + 1) := by
      rw [h]
      exact mul_mem (hconj g) (hfld c)
    refine Or.inr ⟨hb, fun hbγ => hγ ?_⟩
    have h3 := mul_mem (inv_mem hb) hbγ
    rwa [inv_mul_cancel_left] at h3
  · have hbγ : b * γ' ∈ innFieldSubgroup F (r + 1) := by
      have h3 : b * γ' = MulAut.conj g * fieldAutHom F (r + 1) c := by
        rw [h, mul_assoc (MulAut.conj g * γ'), ← hγs c, ← mul_assoc, mul_assoc (MulAut.conj g) γ' γ',
          hγ2, mul_one]
      rw [h3]
      exact mul_mem (hconj g) (hfld c)
    refine Or.inl ⟨hbγ, fun hb => hγ ?_⟩
    have h3 : γ' = (MulAut.conj g)⁻¹ * b * (fieldAutHom F (r + 1) c)⁻¹ := by
      rw [h]
      group
    rw [h3]
    exact mul_mem (mul_mem (inv_mem (hconj g)) hb) (inv_mem (hfld c))

end InnField

theorem omegaMinusGraphCoordinateInput_holds : OmegaMinusGraphCoordinateInput := by
  intro F _ _ _ n hn β γ σ hσ hβ hγ hirr
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  obtain ⟨α, hα, hσα, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirr
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  have hB := congr_minusPlusSim_fieldAutT (r := r) (by omega) hα hαα hσα hβ hγ
  generalize minusPlusSim (r := r) (by omega) hα hαα = B at hB
  refine ⟨(innFieldSubgroup F (r + 1)).comap (MulAut.congr B).toMonoidHom, ?_, fun x => ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (MulAut.congr B).surjective,
      index_innFieldSubgroup (by omega)]
  · refine Subgroup.mem_comap.2 (mem_innFieldSubgroup.2 ⟨B x, 1, ?_⟩)
    rw [map_one, mul_one]
    exact omegaMinus_mulAut_congr_conj B x
  · intro hmem
    have h1 := Subgroup.mem_comap.1 hmem
    change MulAut.congr B _ ∈ innFieldSubgroup F (r + 1) at h1
    rw [hB] at h1
    exact symmetryAut_mul_fieldAutHom_not_mem (by omega) σ h1

theorem omegaMinusFieldRowEndInput_holds : OmegaMinusFieldRowEndInput :=
  omegaMinusFieldRowEndInput_of_graphCoordinate omegaMinusGraphCoordinateInput_holds

end CFSG.SeitzReduction.OmegaPilot
