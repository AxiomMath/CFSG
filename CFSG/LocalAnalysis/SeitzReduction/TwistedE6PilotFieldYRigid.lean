module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYRigidBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldImages
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldY

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (matrix_simple_nonabelian)

local instance twistedE6PilotFieldYRigidNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section FieldPart

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem right_ne_one_of_isComponent
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβ : β * β = 1)
    {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaMinus 4 2 g) {S : similarityPairs (coordinateQuadPlus 4 K)}
    (hS : S ∈ unitMultiplierPairs (coordinateQuadPlus 4 K))
    (hSβ : matrixProjectiveConjugationHom _ S = β) :
    orderOf β = 2 ∧
      β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∧
        S.val.right ≠ 1 := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hE := commutator_coordinateQuadPlus 4 K (by norm_num)
  have hDp := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hβ1 : β ≠ 1 := by
    rintro rfl
    obtain ⟨hs, -⟩ := matrix_simple_nonabelian (by norm_num : 0 < 2 * 4) hQ hT
    exact false_of_isComponent_fixedSubgroup_one (E7Pilot.lieModel_coordinatePlus hf hK le_rfl)
      hD hDm
  have hβ2 : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ) hβ1
  obtain ⟨-, -, -, -, F, hF, hker, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by norm_num : 1 ≤ 2 * 4) _ hQ hT hE
  obtain ⟨-, -, hright⟩ := hinv β hβim hβ2 S hS hSβ
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  have hinn : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
    rintro ⟨z, hz⟩
    have hz1 : z ≠ 1 := fun h => hβ1 (by rw [← hz, h, map_one])
    have hz2 : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ hz1
      apply hcj
      rw [map_pow, hz, pow_two, hβ, map_one]
    have hfree := CatLeaf.involutionCentralizersComponentFree_orthogonal (Or.inl rfl)
      (E7Pilot.statedClassicalModel_coordinatePlus (n := 4) hf hK le_rfl)
    have heq : fixedSubgroup β = centralizer ({z} : Set _) := by
      rw [← hz]
      exact E7Pilot.fixedSubgroup_mulAut_conj_eq z
    exact hfree z hz2 _ (CatLeaf.isComponent_map_mulEquiv (MulEquiv.subgroupCongr heq) hD)
  refine ⟨hβ2, hinn, ?_⟩
  rcases hright with hσ1 | ⟨hord, -, -⟩
  · exfalso
    have hmem : (⟨matrixProjectiveConjugationHom _ S, ⟨S, rfl⟩⟩ :
        matrixProjectiveImage (coordinateQuadPlus 4 K)) ∈ F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ1]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β := hs.trans hSβ
    have hs2 : orderOf (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)) = 2 := by
      rw [hs']
      exact hβ2
    have hso : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) ∉
        OuterAutomorphisms.inner _ := by
      rw [hs']
      exact hinn
    have heq : fixedSubgroup β =
        fixedSubgroup (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)) := by
      rw [hs']
    rcases F4Pilot.omega_linear_fixed hf hK (by norm_num) hQ hT hE s hs2 hso with hΦ | hch
    · obtain ⟨Φ⟩ := hΦ
      exact false_of_component_of_statedSp_omega hK hf (by norm_num : 3 ≤ 4 - 1)
        ((MulEquiv.subgroupCongr heq).trans Φ) hD (Or.inr rfl) hDm
    · exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch _
        (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
          (MulEquiv.subgroupCongr heq) hDp)
  · intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)

end FieldPart

section Rigid

variable
  {f : ℕ} {K : Type} [Field K]

theorem twistedE6_mulAut_mul_conj_mul_inv {P : Type*} [Group P] (φ : MulAut P) (y : P) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  apply MulEquiv.ext
  intro x
  change φ (y * φ⁻¹ x * y⁻¹) = φ y * x * (φ y)⁻¹
  rw [map_mul, map_mul, map_inv]
  change φ y * φ (φ.symm x) * (φ y)⁻¹ = _
  rw [MulEquiv.apply_symm_apply]

theorem fixRigidComm_d4LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    FixRigidComm ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).subtype
      (d4LeviTwist (apply_apply_eq hK hσ)) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨hT, ⟨eT⟩, hA, -⟩ := isComponent_top_fixedSubgroup_d4LeviTwist hf hK hσ
  have hfix := fixedSubgroup_d4LeviTwist hf hK hσ
  have hFF := levelTwist_mul_self (apply_apply_eq hK hσ) perm_mem_setD
  intro α hα hαF
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨f', hf', hK'⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hTs⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hE := commutator_coordinateQuadPlus 4 K (by norm_num)
  have hst : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 2
      f' := ⟨⟨Nat.prime_two, hf', le_rfl⟩, K, inferInstance, inferInstance, hK', ⟨MulEquiv.refl _⟩⟩
  have himg := coordinate_plus_family_eq_matrixImage hst K hK' (MulEquiv.refl _)
  have hEQ : ∀ γ : MulAut (subsystemGroup TwistTag.E6.tag K setD),
      γ * d4LeviTwist (apply_apply_eq hK hσ) = d4LeviTwist (apply_apply_eq hK hσ) * γ →
      MulAut.congr ((d4StatedEquiv K).trans
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit.plusCoordinateEquiv
          4 K)) γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro γ hγ
    have h1 : MulAut.congr (d4StatedEquiv K) γ *
        MulAut.congr (d4StatedEquiv K) (d4LeviTwist (apply_apply_eq hK hσ)) =
        MulAut.congr (d4StatedEquiv K) (d4LeviTwist (apply_apply_eq hK hσ)) *
          MulAut.congr (d4StatedEquiv K) γ := by
      have h0 := congrArg (MulAut.congr (d4StatedEquiv K)) hγ
      exact (map_mul (MulAut.congr (d4StatedEquiv K)) _ _).symm.trans
        (h0.trans (map_mul (MulAut.congr (d4StatedEquiv K)) _ _))
    have h3 := CatalogueBOrthogonalInvolutionConjugacy.congr_mem_pointFamilyAut _
      (smul_statedPointFamily_of_commute hσσ h1)
    rw [himg] at h3
    exact h3
  set Φc := (d4StatedEquiv K).trans
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit.plusCoordinateEquiv 4 K)
    with hΦc
  have hαc := hEQ (d4LeviTwist (apply_apply_eq hK hσ)) rfl
  have hβc := hEQ α hαF
  have hαc2 : MulAut.congr Φc (d4LeviTwist (apply_apply_eq hK hσ)) *
      MulAut.congr Φc (d4LeviTwist (apply_apply_eq hK hσ)) = 1 := by
    have h0 := congrArg (MulAut.congr Φc) hFF
    exact (map_mul (MulAut.congr Φc) _ _).symm.trans (h0.trans (map_one (MulAut.congr Φc)))
  let eF := CatLeafProof.fixedSubgroupCongrEquiv Φc (d4LeviTwist (apply_apply_eq hK hσ))
  have hTc := CFSG.LocalCores.isComponent_map_mulEquiv eF hT
  have hTcm := LieType.CurtisTits.lieModel_of_mulEquiv
    ((⊤ : Subgroup (fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)))).equivMapOfInjective
      eF.toMonoidHom eF.injective) (LieType.CurtisTits.lieModel_of_mulEquiv eT.symm hA)
  obtain ⟨-, -, -, huniq, -, -, -, -, -⟩ :=
    evenOrthogonalRealization_of_regular hf' hK' (by norm_num : 1 ≤ 2 * 4) _ hQ hTs hE
  obtain ⟨S, ⟨hS, hSα⟩, -⟩ := huniq _ hαc
  obtain ⟨hα2, -, hσ1⟩ := right_ne_one_of_isComponent hαc hαc2 hTc hTcm hS hSα
  obtain ⟨-, -, -, -, ext, -, -, -, hinn, hNC, -, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf' hK' (le_rfl : 4 ≤ 4) _ hQ hTs hE _ hαc hα2 S hS
      hSα hσ1
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hTs hE
  have hβcmem : MulAut.congr Φc α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ⊓
      centralizer {MulAut.congr Φc (d4LeviTwist (apply_apply_eq hK hσ))} ⊓
        centralizer ((extKappa (coordinateQuadPlus 4 K) ext).range :
          Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hβc, mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · exact (map_mul (MulAut.congr Φc) _ _).symm.trans
        ((congrArg (MulAut.congr Φc) hαF).symm.trans (map_mul (MulAut.congr Φc) _ _)) |>.symm
    · rw [mem_centralizer_iff]
      intro n hn
      obtain ⟨y, rfl⟩ := hinn hn
      have hnα := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hNC hn)).2
      have hy : MulAut.congr Φc (d4LeviTwist (apply_apply_eq hK hσ)) y = y := by
        apply hcj
        rw [← twistedE6_mulAut_mul_conj_mul_inv, ← hnα, mul_inv_cancel_right]
      have hyF : d4LeviTwist (apply_apply_eq hK hσ) (Φc.symm y) = Φc.symm y := by
        have h1 := congrArg Φc.symm hy
        change Φc.symm (Φc (d4LeviTwist (apply_apply_eq hK hσ) (Φc.symm y))) = Φc.symm y at h1
        rwa [MulEquiv.symm_apply_apply] at h1
      have hmem : Φc.symm y ∈ fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)) := hyF
      rw [hfix] at hmem
      have hαy : α (Φc.symm y) = Φc.symm y := hα ⟨Φc.symm y, hmem⟩
      have hyβ : MulAut.congr Φc α y = y := by
        change Φc (α (Φc.symm y)) = y
        rw [hαy, MulEquiv.apply_symm_apply]
      calc MulAut.conj y * MulAut.congr Φc α =
          MulAut.conj (MulAut.congr Φc α y) * MulAut.congr Φc α := by rw [hyβ]
        _ = MulAut.congr Φc α * MulAut.conj y := by
          rw [← twistedE6_mulAut_mul_conj_mul_inv, inv_mul_cancel_right]
  rw [hcent, mem_zpowers_iff] at hβcmem
  obtain ⟨i, hi⟩ := hβcmem
  have hα2' : MulAut.congr Φc (d4LeviTwist (apply_apply_eq hK hσ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, hαc2]
  rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, _root_.zpow_mul, hα2', _root_.one_zpow] at hi
    apply (MulAut.congr Φc).injective
    rw [← hi, map_one]
  · right
    rw [_root_.zpow_add, _root_.zpow_mul, hα2', _root_.one_zpow, one_mul, zpow_one] at hi
    exact (MulAut.congr Φc).injective hi.symm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem FieldNeighbourIso2E6.pieceCore_eq_map_relLevi_Y' (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} {X : Subgroup G}
    (htL : t ∈ centralizer (L : Set G))
    (h : FieldNeighbourIso2E6 e t X (subsystemGroup TwistTag.E6.tag K setD)
      (d4LeviTwist (apply_apply_eq hK hσ)) (omegaMinusLevi σ))
    {A : Subgroup Kˣ} (hA3 : 3 ≤ Nat.card A) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    {m : ℕ} (hm : Odd m) (hAm : ∀ c ∈ A, c ^ m = 1) {I : Finset (Fin Tag.F4.rank)}
    (hI : I.card ≤ 2) (hIY : I ⊆ {0, 1, 2}) (hXT : X ≤ modelToG e (relLeviTorus K A I)) :
    pieceCore e A I = (((relLevi K I).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).map
      h.Φ.toMonoidHom).map (centralizerPerfectCore X).subtype :=
  h.pieceCore_eq_map_relLevi_Y hK hσ htL (fixRigidComm_d4LeviTwist hf hK hσ) hA3 hAσ hm hAm hI hIY
    hXT

end Rigid

end CFSG.SeitzReduction.TwistedE6Pilot
