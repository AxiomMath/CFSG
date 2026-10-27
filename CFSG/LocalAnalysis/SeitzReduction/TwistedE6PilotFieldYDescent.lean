module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutDescent

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)
open CFSG.GroupTheory.WeirSylow (binForm binForm_isometry quadMinusIsometry)

theorem fieldAutT_congr_right {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    {σ τ : K ≃+* K} (h : σ = τ) (hσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hτ : ∀ v, Q (coordinateFieldMap d τ v) = τ (Q v)) : fieldAutT Q σ hσ = fieldAutT Q τ hτ := by
  subst h
  rfl

theorem false_of_isComponent_fixedSubgroup_one {P : Type}
    [Group P] [IsSimpleGroup P] {n g m f : ℕ} (hP : LieModel P .POmegaPlus n 2 g)
    {D : Subgroup (fixedSubgroup (1 : MulAut P))} (hD : CFSG.IsComponent D)
    (hDm : LieModel D .POmegaMinus m 2 f) : False := by
  have htop : fixedSubgroup (1 : MulAut P) = ⊤ := by
    ext x
    exact ⟨fun _ => mem_top x, fun _ => rfl⟩
  let e₁ : fixedSubgroup (1 : MulAut P) ≃* P :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have : IsSimpleGroup (fixedSubgroup (1 : MulAut P)) := e₁.isSimpleGroup
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* P := ((MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv).trans e₁
  exact false_of_lieModel_omegaPlus_omegaMinus
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hP) hDm

section Image

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulEquiv_congr_eq_fieldAutT_of_mem_image {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {b c : K} (hb : σ b = b) (hc : σ c = c)
    (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβ : β * β = 1)
    {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaMinus 4 2 g) :
    ∃ Θ : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
        matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus 4 K (by norm_num) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hb hc) := by
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
  obtain ⟨-, -, -, huniq, F, hF, hker, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by norm_num : 1 ≤ 2 * 4) _ hQ hT hE
  obtain ⟨S, ⟨hS, hSβ⟩, -⟩ := huniq β hβim
  obtain ⟨hSS, hTT, hright⟩ := hinv β hβim hβ2 S hS hSβ
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  by_cases hinn : β ∈ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K))
  · exfalso
    obtain ⟨z, hz⟩ := hinn
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
  rcases hright with hσ1 | ⟨hord, huniqσ, -⟩
  ·
    exfalso
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
  have hσS : σ = S.val.right := huniqσ σ hσ
  have hσ1 : S.val.right ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus 4 K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * 4 := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨g', hg', hk'⟩ :=
    F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 4
      (by norm_num) hdim with ⟨b', hb'⟩ | ⟨β', γ', -, hroot, b', hb'⟩
  ·
    exfalso
    obtain ⟨eP⟩ := E7Pilot.nonempty_mulEquiv_pairDescentDerived hf hK (by norm_num) hQ hT hE hβim
      hβ2 hinn hS hSβ hσ1 hDp
    have hreg := regular_coordinateQuadPlus 4 (descentField S.val.right) (by norm_num)
    obtain ⟨eM⟩ := E7Pilot.nonempty_derived_mulEquiv_of_isometry hg' hk' (by norm_num) _
      ((plusBasisIsometry b' hb').trans (coordinatePlusIsometry 4 (descentField S.val.right)))
      hreg.1 hreg.2 (commutator_coordinateQuadPlus 4 (descentField S.val.right) (by norm_num))
    exact false_of_lieModel_omegaPlus_omegaMinus
      (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eM).symm
        (E7Pilot.lieModel_coordinatePlus hg' hk' le_rfl)) hDm
  ·
    have hbk : b ∈ descentField S.val.right := by
      rw [mem_descentField, ← hσS]
      exact hb
    have hck : c ∈ descentField S.val.right := by
      rw [mem_descentField, ← hσS]
      exact hc
    have hirr₀ : ∀ s : descentField S.val.right,
        s ^ 2 + ⟨b, hbk⟩ * s + ⟨c, hck⟩ ≠ 0 := by
      intro s hs
      refine hirr s (by rw [hσS]; exact mem_descentField.1 s.2) ?_
      have h1 := congrArg (fun x : descentField S.val.right => (x : K)) hs
      simpa using h1
    obtain ⟨ι⟩ := binForm_isometry hirr₀ hroot
    let φ : (pairDescentForm hS).IsometryEquiv
        (quadMinus 4 (descentField S.val.right) ⟨b, hbk⟩ ⟨c, hck⟩) :=
      (minusBasisIsometry b' hb').trans ((quadMinusIsometry 4 β' γ').trans
        (((QuadraticMap.IsometryEquiv.refl _).prod ι).trans
          (quadMinusIsometry 4 _ _).symm))
    have hQ'σ : ∀ v, coordinateQuadMinus 4 K (by norm_num) b c
        (coordinateFieldMap (2 * 4) S.val.right v) =
          S.val.right (coordinateQuadMinus 4 K (by norm_num) b c v) := by
      rw [← hσS]
      exact coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hb hc
    obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_conj_fieldAutT_of_minus (K := K) (n := 4) (by norm_num) hQ
      hS hσσ hσ1 hTT ⟨b, hbk⟩ ⟨c, hck⟩ φ hQ'σ
    refine ⟨Θ, ?_⟩
    rw [fieldAutT_congr_right _ hσS _ hQ'σ]
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    change Θ (β (Θ.symm (Θ y))) = _
    rw [MulEquiv.symm_apply_apply, ← hSβ]
    exact hΘ y

end Image

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulEquiv_congr_eq_fieldAutT {σ : K ≃+* K} (hσ : orderOf σ = 2) {b c : K}
    (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (hβ : β * β = 1)
    {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaMinus 4 2 g) :
    ∃ Θ : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
        matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus 4 K (by norm_num) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hb hc) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hst : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 2
      f := ⟨⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨γ, hγ⟩ := ((even_orthogonal_involutions_conjugate_into_semilinear_image _ .POmegaPlus
    (Or.inl rfl) 4 f hst).1 K hK (MulEquiv.refl _)).1 β hβ
  have hc' : MulAut.congr γ⁻¹ β = γ⁻¹ * β * γ := MulEquiv.ext fun _ => rfl
  have hβ' : (γ⁻¹ * β * γ) * (γ⁻¹ * β * γ) = 1 := by
    rw [← hc', ← map_mul, hβ, map_one]
  let eF : fixedSubgroup β ≃* fixedSubgroup (γ⁻¹ * β * γ) :=
    (CatLeafProof.fixedSubgroupCongrEquiv γ⁻¹ β).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc'))
  obtain ⟨Θ₁, hΘ₁⟩ := exists_mulEquiv_congr_eq_fieldAutT_of_mem_image hσ hb hc hirr hγ hβ'
    (CFSG.LocalCores.isComponent_map_mulEquiv eF hD)
    (LieType.CurtisTits.lieModel_of_mulEquiv (D.equivMapOfInjective _ eF.injective) hDm)
  refine ⟨(γ⁻¹ : MulAut _).trans Θ₁, ?_⟩
  rw [← hΘ₁, ← hc']
  exact MulEquiv.ext fun _ => rfl

end Descent

end CFSG.SeitzReduction.TwistedE6Pilot
