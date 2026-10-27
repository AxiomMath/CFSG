module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutNormal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightUnique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFlip

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo
  symmetryIsometry symmetryAut)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair
  matrixDerivedConjugation_fieldPair_val)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.Classical2 (orthDerived)

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem fieldAutHom_frameHom (σ : F ≃+* F) (t : Fin n → Fˣ) :
    fieldAutHom F n σ ((isHypFrame_plus F n).frameHom t) =
      (isHypFrame_plus F n).frameHom (liftParam σ.toRingHom t) := by
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply]
  change matrixProjectiveConjugation _ (fieldPair _ σ (E7Pilot.coordinateQuadPlus_fieldMap n σ))
      (matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)) =
    matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change σ ((((derivedEquiv _).symm ⟨_, (isHypFrame_plus F n).frameLin_mem_orthDerived t⟩ :
      matrixDerived _) : GL (Fin (2 * n)) F).val i j) = _
  rw [derivedEquiv_symm_frameLin_entry (isHypFrame_plus F n),
    derivedEquiv_symm_frameLin_entry (isHypFrame_plus F n)]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact (frameEntry_liftParam σ.toRingHom _ _ t j).symm
  · simp only [hij, ↓reduceIte, map_zero]

end Field

section Reflection

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem kappa_isometry_projHom {d : ℕ} {Q : QuadraticForm F (Fin d → F)} (A : matrixIsometries Q)
    (z : orthDerived Q)
    (hz : matrixLinearIso (A : GL (Fin d) F) * (z : (Fin d → F) ≃ₗ[F] (Fin d → F)) *
      (matrixLinearIso (A : GL (Fin d) F))⁻¹ ∈ orthDerived Q) :
    matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A) (projHom Q z) =
      projHom Q ⟨_, hz⟩ := by
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q ((derivedEquiv Q).symm z)) =
    matrixProjectiveProjection Q ((derivedEquiv Q).symm ⟨_, hz⟩)
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply (derivedEquiv Q).injective
  apply Subtype.ext
  rw [MulEquiv.apply_symm_apply, coe_derivedEquiv, matrixDerivedConjugation_val]
  change matrixLinearIso ((A : GL (Fin d) F) * glFieldAut (Fin d) F 1
      ((derivedEquiv Q).symm z : matrixDerived Q).val * (A : GL (Fin d) F)⁻¹) = _
  rw [map_one, MulAut.one_apply, map_mul, map_mul, map_inv, ← coe_derivedEquiv,
    MulEquiv.apply_symm_apply]

theorem symmetryGL_lastPlaneVec_eq_swapLin {r : ℕ} :
    matrixLinearIso (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)) =
      swapLin (plusIndexEquiv (r + 1) (.inl (Fin.last r)))
        (plusIndexEquiv (r + 1) (.inr (Fin.last r))) := by
  have hv : coordinateQuadPlus (r + 1) F (lastPlaneVec r) = 1 := coordinateQuadPlus_lastPlaneVec
  set p := plusIndexEquiv (r + 1) (.inl (Fin.last r)) with hp
  set q := plusIndexEquiv (r + 1) (.inr (Fin.last r)) with hq
  have hpq : p ≠ q := fun h => Sum.inl_ne_inr ((plusIndexEquiv _).injective h)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply LinearEquiv.ext
  intro w
  funext i
  rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.matrixLinearIso_apply_eq,
    matrixLinearEquiv_apply, symmetryGL_mulVec_of_charTwo hv, swapLin_apply, polar_lastPlaneVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lastPlaneVec, Pi.single_apply]
  rw [← hp, ← hq]
  by_cases hip : i = p
  · subst hip
    rw [Equiv.swap_apply_left]
    simp only [↓reduceIte, hpq]
    linear_combination (w p) * h2
  · by_cases hiq : i = q
    · subst hiq
      rw [Equiv.swap_apply_right]
      simp only [↓reduceIte, hip]
      linear_combination (w q) * h2
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
      simp only [hip, hiq, ↓reduceIte]
      ring

theorem swapLin_mul_frameLin_mul_swapLin {r : ℕ} (t : Fin (r + 1) → Fˣ) :
    swapLin (plusIndexEquiv (r + 1) (.inl (Fin.last r)))
        (plusIndexEquiv (r + 1) (.inr (Fin.last r))) *
      frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) t *
      swapLin (plusIndexEquiv (r + 1) (.inl (Fin.last r)))
        (plusIndexEquiv (r + 1) (.inr (Fin.last r))) =
    frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) (flipParam F {Fin.last r} t) := by
  have hfr := isHypFrame_plus (K := F) (n := r + 1)
  apply LinearEquiv.ext
  intro w
  funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, swapLin_apply, frameLin_apply, swapLin_apply,
    frameLin_apply, Equiv.swap_apply_self]
  congr 2
  obtain ⟨k | k, rfl⟩ := (plusIndexEquiv (r + 1)).surjective i
  · by_cases hk : k = Fin.last r
    · subst hk
      rw [Equiv.swap_apply_left]
      have e1 := hfr.frameEntry_right t (Fin.last r)
      have e2 := hfr.frameEntry_left (flipParam F {Fin.last r} t) (Fin.last r)
      simp only [plusFrameLeft, plusFrameRight] at e1 e2
      rw [e1, e2, flipParam_apply]
      simp
    · have hne1 : plusIndexEquiv (r + 1) (.inl k) ≠ plusIndexEquiv (r + 1) (.inl (Fin.last r)) :=
        fun h => hk (Sum.inl_injective ((plusIndexEquiv _).injective h))
      have hne2 : plusIndexEquiv (r + 1) (.inl k) ≠ plusIndexEquiv (r + 1) (.inr (Fin.last r)) :=
        fun h => Sum.inl_ne_inr ((plusIndexEquiv _).injective h)
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      have e1 := hfr.frameEntry_left t k
      have e2 := hfr.frameEntry_left (flipParam F {Fin.last r} t) k
      simp only [plusFrameLeft] at e1 e2
      rw [e1, e2, flipParam_apply]
      simp [hk]
  · by_cases hk : k = Fin.last r
    · subst hk
      rw [Equiv.swap_apply_right]
      have e1 := hfr.frameEntry_left t (Fin.last r)
      have e2 := hfr.frameEntry_right (flipParam F {Fin.last r} t) (Fin.last r)
      simp only [plusFrameLeft, plusFrameRight] at e1 e2
      rw [e1, e2, flipParam_apply]
      simp
    · have hne1 : plusIndexEquiv (r + 1) (.inr k) ≠ plusIndexEquiv (r + 1) (.inl (Fin.last r)) :=
        fun h => Sum.inr_ne_inl ((plusIndexEquiv _).injective h)
      have hne2 : plusIndexEquiv (r + 1) (.inr k) ≠ plusIndexEquiv (r + 1) (.inr (Fin.last r)) :=
        fun h => hk (Sum.inr_injective ((plusIndexEquiv _).injective h))
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      have e1 := hfr.frameEntry_right t k
      have e2 := hfr.frameEntry_right (flipParam F {Fin.last r} t) k
      simp only [plusFrameRight] at e1 e2
      rw [e1, e2, flipParam_apply]
      simp [hk]

theorem symmetryAut_lastPlaneVec_frameHom {r : ℕ} (t : Fin (r + 1) → Fˣ) :
    symmetryAut (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)
        ((isHypFrame_plus F (r + 1)).frameHom t) =
      (isHypFrame_plus F (r + 1)).frameHom (flipParam F {Fin.last r} t) := by
  have hlin : matrixLinearIso (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)) *
      frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) t *
      (matrixLinearIso (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)))⁻¹ =
      frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) (flipParam F {Fin.last r} t) := by
    rw [symmetryGL_lastPlaneVec_eq_swapLin, swapLin_inv, swapLin_mul_frameLin_mul_swapLin]
  have hz : matrixLinearIso (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)) *
      frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) t *
      (matrixLinearIso (symmetryGL (coordinateQuadPlus (r + 1) F) (lastPlaneVec r)))⁻¹ ∈
        orthDerived (coordinateQuadPlus (r + 1) F) := by
    rw [hlin]
    exact (isHypFrame_plus F (r + 1)).frameLin_mem_orthDerived _
  have h1 := kappa_isometry_projHom
    (symmetryIsometry (coordinateQuadPlus (r + 1) F) (lastPlaneVec r))
    ⟨_, (isHypFrame_plus F (r + 1)).frameLin_mem_orthDerived t⟩ hz
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply]
  exact h1.trans (congrArg (projHom _) (Subtype.ext hlin))

end Reflection

section Nodes

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem map_plusFrameTorus_of_frameHom {n : ℕ}
    {δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    {φ : (Fin n → Fˣ) → (Fin n → Fˣ)}
    (hδ : ∀ t, δ ((isHypFrame_plus F n).frameHom t) = (isHypFrame_plus F n).frameHom (φ t))
    {P P' : Subgroup (Fin n → Fˣ)} (h1 : ∀ t ∈ P, φ t ∈ P')
    (h2 : ∀ t' ∈ P', ∃ t ∈ P, φ t = t') :
    (plusFrameTorus F P).map δ.toMonoidHom = plusFrameTorus F P' := by
  rw [plusFrameTorus, plusFrameTorus, (isHypFrame_plus F n).frameTorusOf_eq_map,
    (isHypFrame_plus F n).frameTorusOf_eq_map]
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨φ t, h1 t ht, (hδ t).symm⟩
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨t, ht, rfl⟩ := h2 t' ht'
    exact ⟨_, ⟨t, ht, rfl⟩, hδ t⟩

theorem map_fieldAutHom_plusSignedLevelTorus {n : ℕ} (σ : F ≃+* F) (J P : Finset (Fin n)) :
    (plusSignedLevelTorus F J P).map (fieldAutHom F n σ).toMonoidHom =
      plusSignedLevelTorus F J P := by
  rw [plusSignedLevelTorus]
  refine map_plusFrameTorus_of_frameHom (φ := liftParam σ.toRingHom) (fieldAutHom_frameHom σ)
    (fun t ht => liftParam_mem_signedLevelParam σ.toRingHom ht)
    (fun t' ht' => ⟨liftParam σ.symm.toRingHom t',
      liftParam_mem_signedLevelParam σ.symm.toRingHom ht', ?_⟩)
  funext i
  apply Units.ext
  simp [liftParam]

theorem flipParam_flipParam_eq_symmDiff {n : ℕ} (P S : Finset (Fin n)) (t : Fin n → Fˣ) :
    flipParam F P (flipParam F S t) = flipParam F (symmDiff P S) t := by
  funext i
  simp only [flipParam_apply, Finset.mem_symmDiff]
  by_cases hP : i ∈ P <;> by_cases hS : i ∈ S <;> simp [hP, hS]

theorem signedLevelParam_congr_of_inter {n : ℕ} {J P P' : Finset (Fin n)}
    (h : ∀ i ∈ J, (i ∈ P ↔ i ∈ P')) :
    signedLevelParam (K := F) J P = signedLevelParam J P' := by
  have e : ∀ t : Fin n → Fˣ, ∀ i ∈ J, flipParam F P t i = flipParam F P' t i := by
    intro t i hi
    rw [flipParam_apply, flipParam_apply]
    by_cases hP : i ∈ P
    · simp only [hP, (h i hi).1 hP, ↓reduceIte]
    · have hP' : i ∉ P' := fun h' => hP ((h i hi).2 h')
      simp only [hP, hP', ↓reduceIte]
  ext t
  change (∀ i ∈ J, ∀ k ∈ J, flipParam F P t i = flipParam F P t k) ↔
    (∀ i ∈ J, ∀ k ∈ J, flipParam F P' t i = flipParam F P' t k)
  constructor
  · intro H i hi k hk
    rw [← e t i hi, ← e t k hk]
    exact H i hi k hk
  · intro H i hi k hk
    rw [e t i hi, e t k hk]
    exact H i hi k hk

theorem map_symmetryAut_plusSignedLevelTorus (J P : Finset (Fin 4)) :
    (plusSignedLevelTorus F J P).map
        (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)).toMonoidHom =
      plusSignedLevelTorus F J (symmDiff P {Fin.last 3}) := by
  rw [plusSignedLevelTorus, plusSignedLevelTorus]
  refine map_plusFrameTorus_of_frameHom (n := 4) (φ := flipParam F {Fin.last 3})
    (fun t => symmetryAut_lastPlaneVec_frameHom (r := 3) t) (fun t ht => ?_)
    (fun t' ht' => ⟨flipParam F {Fin.last 3} t', ?_, flipParam_flipParam _ _⟩)
  · change flipParam F (symmDiff P {Fin.last 3}) (flipParam F {Fin.last 3} t) ∈ levelParam J
    rw [flipParam_flipParam_eq_symmDiff, symmDiff_symmDiff_cancel_right]
    exact ht
  · change flipParam F P (flipParam F {Fin.last 3} t') ∈ levelParam J
    rw [flipParam_flipParam_eq_symmDiff]
    exact ht'

theorem exists_map_symmetryAut_nodeTorus (j : Fin 4) :
    ∃ j' : Fin 4,
      (plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)).map
          (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)).toMonoidHom =
        plusSignedLevelTorus F (plusNodeSet 4 j') (plusNodeFlip 4 j') := by
  rw [map_symmetryAut_plusSignedLevelTorus]
  refine ⟨if j = 2 then 3 else if j = 3 then 2 else j, ?_⟩
  have hset : ∀ j : Fin 4,
      plusNodeSet 4 j = plusNodeSet 4 (if j = 2 then 3 else if j = 3 then 2 else j) := by
    decide
  have hflip : ∀ j : Fin 4, ∀ i ∈ plusNodeSet 4 j,
      (i ∈ symmDiff (plusNodeFlip 4 j) {Fin.last 3} ↔
        i ∈ plusNodeFlip 4 (if j = 2 then 3 else if j = 3 then 2 else j)) := by
    decide
  rw [plusSignedLevelTorus, plusSignedLevelTorus, signedLevelParam_congr_of_inter (hflip j),
    ← hset j]

end Nodes

section TriRoot

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (projectivePointFamily)
open scoped Pointwise

theorem map_map_conj_eq_mulAut {X : Type*} [Group X] (δ : MulAut X) (x : X) (H : Subgroup X) :
    (H.map (MulAut.conj x).toMonoidHom).map δ.toMonoidHom =
      (H.map δ.toMonoidHom).map (MulAut.conj (δ x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem map_conj_map_conj_mulAut {X : Type*} [Group X] (x y : X) (H : Subgroup X) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      H.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def PermutesNodeTori (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))) :
    Prop :=
  ∀ j : Fin 4, ∃ (j' : Fin 4) (x : matrixProjectiveDerived (coordinateQuadPlus 4 F)),
    (plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)).map δ.toMonoidHom =
      (plusSignedLevelTorus F (plusNodeSet 4 j') (plusNodeFlip 4 j')).map
        (MulAut.conj x).toMonoidHom

theorem PermutesNodeTori.mul {δ₁ δ₂ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (h₁ : PermutesNodeTori δ₁) (h₂ : PermutesNodeTori δ₂) : PermutesNodeTori (δ₁ * δ₂) := by
  intro j
  obtain ⟨j₁, x₁, hx₁⟩ := h₂ j
  obtain ⟨j₂, x₂, hx₂⟩ := h₁ j₁
  refine ⟨j₂, δ₁ x₁ * x₂, ?_⟩
  have e : (δ₁ * δ₂).toMonoidHom = δ₁.toMonoidHom.comp δ₂.toMonoidHom := rfl
  rw [e, ← Subgroup.map_map, hx₁, map_map_conj_eq_mulAut, hx₂, map_conj_map_conj_mulAut]

theorem permutesNodeTori_conj (g : matrixProjectiveDerived (coordinateQuadPlus 4 F)) :
    PermutesNodeTori (MulAut.conj g) :=
  fun j => ⟨j, g, rfl⟩

theorem permutesNodeTori_of_map_eq
    {δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (h : ∀ j : Fin 4, ∃ j' : Fin 4,
      (plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)).map δ.toMonoidHom =
        plusSignedLevelTorus F (plusNodeSet 4 j') (plusNodeFlip 4 j')) :
    PermutesNodeTori δ := by
  intro j
  obtain ⟨j', h'⟩ := h j
  refine ⟨j', 1, ?_⟩
  rw [h']
  ext y
  simp [Subgroup.mem_map]

theorem permutesNodeTori_one :
    PermutesNodeTori (1 : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))) := by
  have h := permutesNodeTori_conj (F := F) 1
  rwa [map_one] at h

theorem permutesNodeTori_fieldAutHom (σ : F ≃+* F) : PermutesNodeTori (fieldAutHom F 4 σ) :=
  permutesNodeTori_of_map_eq fun j => ⟨j, map_fieldAutHom_plusSignedLevelTorus σ _ _⟩

theorem permutesNodeTori_symmetryAut :
    PermutesNodeTori (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)) :=
  permutesNodeTori_of_map_eq exists_map_symmetryAut_nodeTorus

theorem permutesNodeTori_of_mem_closure
    {τ κ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))} (hτ3 : τ ^ 3 = 1)
    (hκ2 : κ * κ = 1) (hτ : PermutesNodeTori τ) (hκ : PermutesNodeTori κ)
    {π : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (hπ : π ∈ closure ({τ, κ} : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))))) :
    PermutesNodeTori π := by
  have hτinv : τ⁻¹ = τ * τ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← sq, ← pow_succ']
    exact hτ3
  have hκinv : κ⁻¹ = κ := inv_eq_of_mul_eq_one_right hκ2
  induction hπ using closure_induction_left with
  | one => exact permutesNodeTori_one
  | mul_left a ha y hy ih =>
    rcases ha with ha | ha
    · rw [ha]
      exact hτ.mul ih
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hκ.mul ih
  | inv_mul_cancel a ha y hy ih =>
    rcases ha with ha | ha
    · rw [ha, hτinv]
      exact (hτ.mul hτ).mul ih
    · rw [Set.mem_singleton_iff] at ha
      rw [ha, hκinv]
      exact hκ.mul ih

theorem plusFourTriRootInput_of_triality (htri : PlusFourTrialityInput) :
    PlusFourTriRootInput := by
  intro K _ _ _ _ δ j
  obtain ⟨τ, hτ3, hτx, hτs, hκτ, hτT⟩ := htri K
  obtain ⟨-, -, -, -, hNF⟩ := normalForm_four_of_triality hτ3 hτx hτs hκτ
  obtain ⟨g, π, hπ, σ, rfl⟩ := hNF δ
  have hκ2 : symmetryAut (coordinateQuadPlus 4 K) (lastPlaneVec 3) *
      symmetryAut (coordinateQuadPlus 4 K) (lastPlaneVec 3) = 1 := by
    rw [← sq]
    exact CFSG.ComponentClassification.UnbalancedCatalog.symmetryAut_sq _ _
  have hπT := permutesNodeTori_of_mem_closure hτ3 hκ2 hτT permutesNodeTori_symmetryAut hπ
  exact (((permutesNodeTori_conj g).mul hπT).mul (permutesNodeTori_fieldAutHom σ)) j

theorem omegaPlusFourUniqueInput_of_triality (hlin : OmegaPlusLinearInvolutionInput 4)
    (htri : PlusFourTrialityInput) : OmegaPlusFourUniqueInput :=
  omegaPlusFourUniqueInput_of_inputs hlin (plusFourTriRootInput_of_triality htri)

end TriRoot

end CFSG.SeitzReduction.OmegaPilot
