module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponentsSpaces
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry
open CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

section Block

open Matrix

variable {F : Type*} [Field F] {a k : ℕ}

@[expose] def blockDiagOne (M : Matrix (Fin a) (Fin a) F) : Matrix (Fin (a + k)) (Fin (a + k)) F :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks M 0 0 1)

theorem blockDiagOne_mul (M N : Matrix (Fin a) (Fin a) F) :
    blockDiagOne (k := k) (M * N) = blockDiagOne M * blockDiagOne N := by
  simp only [blockDiagOne, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blockDiagOne_one : blockDiagOne (k := k) (1 : Matrix (Fin a) (Fin a) F) = 1 := by
  simp [blockDiagOne, fromBlocks_one]

theorem det_blockDiagOne (M : Matrix (Fin a) (Fin a) F) :
    (blockDiagOne (k := k) M).det = M.det := by
  simp [blockDiagOne]

theorem blockDiagOne_apply_castAdd (M : Matrix (Fin a) (Fin a) F) (i j : Fin a) :
    blockDiagOne (k := k) M (Fin.castAdd k i) (Fin.castAdd k j) = M i j := by
  simp [blockDiagOne]

theorem blockDiagOne_apply_natAdd (M : Matrix (Fin a) (Fin a) F) (i : Fin k) :
    blockDiagOne (k := k) M (Fin.natAdd a i) (Fin.natAdd a i) = 1 := by
  simp [blockDiagOne]

theorem conjTr_blockDiagOne (σ : F ≃+* F) (M : Matrix (Fin a) (Fin a) F) :
    conjTr σ (blockDiagOne (k := k) M) = blockDiagOne (conjTr σ M) := by
  rw [conjTr, conjTr, blockDiagOne, blockDiagOne, reindex_apply, reindex_apply, ← submatrix_map,
    transpose_submatrix, fromBlocks_map, fromBlocks_transpose, Matrix.map_zero _ (map_zero σ),
    Matrix.map_zero _ (map_zero σ), Matrix.map_one _ (map_zero σ) (map_one σ), transpose_zero,
    transpose_zero, transpose_one]

@[expose] def blockDiagOneHom : Matrix (Fin a) (Fin a) F →* Matrix (Fin (a + k)) (Fin (a + k)) F
    where
  toFun := blockDiagOne
  map_one' := blockDiagOne_one
  map_mul' := blockDiagOne_mul

theorem blockDiagOne_mem_SUid (σ : F ≃+* F) {g : GL (Fin a) F} (hg : g ∈ SUid σ a) :
    Units.map (blockDiagOneHom (k := k)) g ∈ SUid σ (a + k) := by
  obtain ⟨hdet, hiso⟩ := hg
  refine ⟨?_, ?_⟩
  · change (blockDiagOne (g : Matrix (Fin a) (Fin a) F)).det = 1
    rw [det_blockDiagOne, hdet]
  · change conjTr σ (blockDiagOne (g : Matrix (Fin a) (Fin a) F)) *
      blockDiagOne (g : Matrix (Fin a) (Fin a) F) = 1
    rw [conjTr_blockDiagOne, ← blockDiagOne_mul, hiso, blockDiagOne_one]

@[expose] def blockDiagOneSUid (σ : F ≃+* F) : SUid σ a →* SUid σ (a + k) :=
  ((Units.map (blockDiagOneHom (k := k))).comp (SUid σ a).subtype).codRestrict _
    fun g => blockDiagOne_mem_SUid σ g.2

end Block

theorem exists_quaternion_statedProj {F : Type} [Field F] (hF2 : (2 : F) ≠ 0) (σ : F ≃+* F)
    {m q : ℕ} (hm : 3 ≤ m) (hSU : SUid σ m = StatedSU m q F) {a b : F} (ha : σ a = -a)
    (hb : σ b = -b) (hab : a ^ 2 + b ^ 2 = -1) :
    ∃ φ : QuaternionGroup 2 →* StatedProj (StatedSU m q F), Function.Injective φ := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
  have hxmem : Matrix.SpecialLinearGroup.toGL
      (LocalAnalysis.ComponentInitial.QuaternionMatrices.slQuatI F) ∈ SUid σ 2 := by
    refine ⟨LocalAnalysis.ComponentInitial.QuaternionMatrices.det_quatI, ?_⟩
    change conjTr σ (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatI F) *
      LocalAnalysis.ComponentInitial.QuaternionMatrices.quatI F = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, LocalAnalysis.ComponentInitial.QuaternionMatrices.quatI, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hymem : Matrix.SpecialLinearGroup.toGL
      (LocalAnalysis.ComponentInitial.QuaternionMatrices.slQuatJ hab) ∈ SUid σ 2 := by
    refine ⟨LocalAnalysis.ComponentInitial.QuaternionMatrices.det_quatJ hab, ?_⟩
    change conjTr σ (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ a b) *
      LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ a b = 1
    have hc : conjTr σ (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ a b) =
        -LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ a b := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ, ha, hb]
    rw [hc, Matrix.neg_mul, LocalAnalysis.ComponentInitial.QuaternionMatrices.quatJ_mul_self hab,
      neg_neg]
  have hmem : ∀ g, Matrix.SpecialLinearGroup.toGL
      (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab g) ∈ SUid σ 2 := by
    intro g
    rcases g with i | i
    · rw [LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom,
        LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift_a, map_pow]
      exact pow_mem hxmem _
    · rw [LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom,
        LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift_xa, map_mul, map_pow]
      exact mul_mem hymem (pow_mem hxmem _)
  let f2 : QuaternionGroup 2 →* SUid σ 2 :=
    (Matrix.SpecialLinearGroup.toGL.comp
      (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab)).codRestrict _ hmem
  let φ : QuaternionGroup 2 →* StatedProj (StatedSU (2 + k) q F) :=
    (QuotientGroup.mk' _).comp ((MulEquiv.subgroupCongr hSU).toMonoidHom.comp
      ((blockDiagOneSUid (k := k) σ).comp f2))
  refine ⟨φ, OddSelector.injective_of_quaternion φ fun h1 => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  change Matrix.GeneralLinearGroup.scalar (Fin (2 + k)) c = Units.map (blockDiagOneHom (k := k))
    (Matrix.SpecialLinearGroup.toGL
      (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab (QuaternionGroup.a 2))) at hc
  have hk : 0 < k := by omega
  have e1 := congrArg (fun g : GL (Fin (2 + k)) F =>
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) F) (Fin.castAdd k 0) (Fin.castAdd k 0)) hc
  have e2 := congrArg (fun g : GL (Fin (2 + k)) F =>
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) F) (Fin.natAdd 2 ⟨0, hk⟩) (Fin.natAdd 2 ⟨0, hk⟩)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.coe_map] at e1 e2
  change (c : F) = blockDiagOne (k := k)
    ((LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab (QuaternionGroup.a 2) :
      Matrix (Fin 2) (Fin 2) F)) (Fin.castAdd k 0) (Fin.castAdd k 0) at e1
  change (c : F) = blockDiagOne (k := k)
    ((LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab (QuaternionGroup.a 2) :
      Matrix (Fin 2) (Fin 2) F)) (Fin.natAdd 2 ⟨0, hk⟩) (Fin.natAdd 2 ⟨0, hk⟩) at e2
  rw [blockDiagOne_apply_castAdd, LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom_a_two,
    Matrix.neg_apply, Matrix.one_apply_eq] at e1
  rw [blockDiagOne_apply_natAdd] at e2
  apply hF2
  linear_combination e1 - e2

variable {E : Type} [Field E] [Finite E] {W : Type} [AddCommGroup W] [Module E W]
  [FiniteDimensional E W] {sigma : E ≃+* E}

theorem nonempty_quotient_psu {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 3 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {Y : Subgroup (isometryGroup h)} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) :
    Nonempty (X ⧸ center X ≃* StatedProj (StatedSU (finrank E W) (ℓ ^ e) E)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP E ℓ := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hE
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E ℓ]; exact hℓ2)
  have hq2 : ℓ ^ e ≠ 2 := fun h2 =>
    hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (h2 ▸ dvd_pow_self ℓ (by omega)))
  have hnq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2 := by
    intro h2
    have : Fintype (CatalogueBLinearTwoDescent.fixedSubfield E sigma) := Fintype.ofFinite _
    have h0 := FiniteField.cast_card_eq_zero (CatalogueBLinearTwoDescent.fixedSubfield E sigma)
    rw [← Nat.card_eq_fintype_card, h2] at h0
    have h3 := congrArg (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype h0
    rw [map_natCast, map_zero] at h3
    exact hE2 (by exact_mod_cast h3)
  have hnq : (finrank E W, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) ≠
      (3, 2) := fun h3 => hnq2 (congrArg Prod.snd h3)
  have hq := specialIsometry_quasisimple_of_three_le h hsym hnd hsigma hne hW hnq
  have hcomm : commutator (isometryGroup h) = specialIsometry h := by
    refine le_antisymm (Abelianization.commutator_subset_ker _) ?_
    calc specialIsometry h = ⁅specialIsometry h, specialIsometry h⁆ :=
          (Subgroup.isPerfect_iff.mp hq.1).symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = _ := (_root_.commutator_def _).symm
  have hYeq : Y = specialIsometry h :=
    (LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY (hcomm ▸ hq)).trans hcomm
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hsigma hne
  have hsigU : sigma = CFSG.LieType.BorelTits.unitaryInvolution E ℓ e :=
    RingEquiv.ext fun z => by rw [hsig, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hSU : SUid sigma (finrank E W) = StatedSU (finrank E W) (ℓ ^ e) E := by
    rw [hsigU]
    exact SUid_eq_statedSU hE _
  let eYS : Y ≃* StatedSU (finrank E W) (ℓ ^ e) E :=
    ((MulEquiv.subgroupCongr hYeq).trans (specialIsometryMatrixEquiv h b hb)).trans
      (MulEquiv.subgroupCongr hSU)
  have hqS := SUid_quasisimple_finite sigma hsigma hne (finrank E W) hW hnq
  have : Group.IsPerfect (SUid sigma (finrank E W)) := hqS.1
  have hperf : Group.IsPerfect (StatedSU (finrank E W) (ℓ ^ e) E) :=
    Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hSU).toMonoidHom)
      (MulEquiv.subgroupCongr hSU).surjective
  have hsimple := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E ℓ e hE
    (finrank E W) hW (fun h3 => hq2 (congrArg Prod.snd h3))
  have hZ := (isQuasisimple_statedSU hperf hsimple).2
  obtain ⟨e0⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hY.1 σ hσs hσk
  exact ⟨e0.symm.trans ((QuotientGroup.congr (center Y) (center _) eYS
    (Subgroup.map_center_eq eYS)).trans (QuotientGroup.quotientMulEquivOfEq hZ))⟩

theorem unitary_component_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 4 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {Y : Subgroup (isometryGroup h)} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) : False := by
  classical
  obtain ⟨eX⟩ := nonempty_quotient_psu hℓ hℓ2 he hE (by omega) h hsym hnd hsigma hne hsig hY σ
    hσs hσk
  have hud : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ e E :=
    ⟨hℓ, he, by rw [hE, ← pow_mul, mul_comm]⟩
  obtain ⟨E₀, hE₀, hE₀c⟩ := OddSelector.exists_elementary_unitaryPSU hud hℓ2 (n := finrank E W)
    (by omega)
  have hdvd : ℓ ^ 3 ∣ Nat.card (unitaryPSU hud (finrank E W)) := by
    rw [Nat.card_congr (unitaryPSUEquiv hud (n := finrank E W) (by omega)).toEquiv]
    exact OddSelector.prime_cube_dvd_card_psu hℓ he hE (by omega)
  exact false_of_smallSource hs (OddSelector.not_small_source_of_mulEquiv
    (eX.trans (unitaryPSUEquiv hud (by omega)).symm) E₀ hE₀c hℓ hℓ2 hdvd)

theorem unitary_component_false_of_quaternion {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 3 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    (hab : ∃ a b : E, sigma a = -a ∧ sigma b = -b ∧ a ^ 2 + b ^ 2 = -1)
    {Y : Subgroup (isometryGroup h)} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) : False := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP E ℓ := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hE
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E ℓ]; exact hℓ2)
  obtain ⟨eX⟩ := nonempty_quotient_psu hℓ hℓ2 he hE hW h hsym hnd hsigma hne hsig hY σ hσs hσk
  obtain ⟨a, b, ha, hb, hab'⟩ := hab
  have hsigU : sigma = CFSG.LieType.BorelTits.unitaryInvolution E ℓ e :=
    RingEquiv.ext fun z => by rw [hsig, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hSU : SUid sigma (finrank E W) = StatedSU (finrank E W) (ℓ ^ e) E := by
    rw [hsigU]
    exact SUid_eq_statedSU hE _
  obtain ⟨φ, hφ⟩ := exists_quaternion_statedProj hE2 sigma hW hSU ha hb hab'
  have hdvd : ℓ ^ 3 ∣ Nat.card (X ⧸ center X) := by
    rw [Nat.card_congr eX.toEquiv]
    exact OddSelector.prime_cube_dvd_card_psu hℓ he hE hW
  exact false_of_smallSource hs ⟨fun p f hp2 => OddSelector.not_psl_two_odd_of_quaternion
    (eX.symm.toMonoidHom.comp φ) (eX.symm.injective.comp hφ) hp2,
    OddSelector.isEmpty_alternating_seven_of_dvd hℓ hℓ2 hdvd,
    OddSelector.not_psl_three_four_of_dvd hℓ hℓ2 hdvd⟩

theorem unitary_component_false_of_quaternion_equiv {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 3 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    (hab : ∃ a b : E, sigma a = -a ∧ sigma b = -b ∧ a ^ 2 + b ^ 2 = -1)
    {H : Type*} [Group H] (F : H ≃* isometryGroup h) {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) : False := by
  let e2 := Y.equivMapOfInjective F.toMonoidHom F.injective
  exact unitary_component_false_of_quaternion hℓ hℓ2 he hE hW h hsym hnd hsigma hne hsig hab
    (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent F hY)
    (σ.comp e2.symm.toMonoidHom) (hσs.comp e2.symm.surjective)
    (ker_comp_le_center e2.symm.toMonoidHom e2.symm.injective σ hσk) hs

end CFSG.ComponentClassification.OddClassSelector
