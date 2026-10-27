module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutDescent

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.SeitzReduction.E7Pilot

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_conj_eq_fieldAutT_of_component_of_mem_image {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hn : 4 ≤ n) {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n K)) (hβ : β * β = 1)
    (hβ1 : β ≠ 1) {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaPlus n 2 g) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldMap n σ) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hDp := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hβ2 : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ) hβ1
  obtain ⟨-, -, -, huniq, F, hF, hker, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega : 1 ≤ 2 * n) _ hQ hT hE
  obtain ⟨S, ⟨hS, hSβ⟩, -⟩ := huniq β hβim
  obtain ⟨hSS, hTT, hright⟩ := hinv β hβim hβ2 S hS hSβ
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  by_cases hinn : β ∈ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus n K))
  · exfalso
    obtain ⟨z, hz⟩ := hinn
    have hz1 : z ≠ 1 := fun h => hβ1 (by rw [← hz, h, map_one])
    have hz2 : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ hz1
      apply hcj
      rw [map_pow, hz, pow_two, hβ, map_one]
    have hfree := CatLeaf.involutionCentralizersComponentFree_orthogonal (Or.inl rfl)
      (statedClassicalModel_coordinatePlus (n := n) hf hK (by omega))
    have heq : fixedSubgroup β = centralizer ({z} : Set _) := by
      rw [← hz]
      exact fixedSubgroup_mulAut_conj_eq z
    exact hfree z hz2 _ (CatLeaf.isComponent_map_mulEquiv (MulEquiv.subgroupCongr heq) hD)
  rcases hright with hσ1 | ⟨hord, huniqσ, -⟩
  ·
    exfalso
    have hmem : (⟨matrixProjectiveConjugationHom _ S, ⟨S, rfl⟩⟩ :
        matrixProjectiveImage (coordinateQuadPlus n K)) ∈ F.ker := by
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
    rcases F4Pilot.omega_linear_fixed hf hK (by omega) hQ hT hE s hs2 hso with hΦ | hch
    · obtain ⟨Φ⟩ := hΦ
      exact false_of_component_of_statedSp hK hf (by omega : 3 ≤ n - 1)
        ((MulEquiv.subgroupCongr heq).trans Φ) hD hDm
    · exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch _
        (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
          (MulEquiv.subgroupCongr heq) hDp)
  have hσS : σ = S.val.right := huniqσ σ hσ
  have hσ1 : S.val.right ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 n
      (by omega) hdim with ⟨b, hb⟩ | ⟨β', γ', -, hroot, b, hb⟩
  ·
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_plus (by omega) hS hσσ hσ1 hTT b hb
    refine ⟨ψ, ?_⟩
    rw [← hSβ, hψ, hσS]
  ·
    exfalso
    obtain ⟨g', hg', hk'⟩ :=
      F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
    obtain ⟨eP⟩ := nonempty_mulEquiv_pairDescentDerived hf hK (by omega) hQ hT hE hβim hβ2 hinn
      hS hSβ hσ1 hDp
    have hreg := regular_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega) hroot
    obtain ⟨eM⟩ := nonempty_derived_mulEquiv_of_isometry hg' hk' (by omega) _
      ((minusBasisIsometry b hb).trans
        (coordinateMinusIsometry n (descentField S.val.right) (by omega) β' γ'))
      hreg.1 hreg.2 (commutator_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega)
        hroot)
    have hmM : LieModel (matrixProjectiveDerived (coordinateQuadMinus n (descentField S.val.right)
        (by omega) β' γ')) .POmegaMinus n 2 g' :=
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg', by omega⟩, descentField S.val.right, inferInstance,
        inferInstance, hk', β', γ', hroot,
        ⟨(coordinateMinusWitnessEquiv _ (by omega) β' γ' (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨htt, -, -⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
      (Or.inl rfl) hDm (Or.inl (by decide))
      (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eM).symm hmM) rfl
    exact absurd htt (by decide)

theorem exists_conj_eq_fieldAutT_of_component_four {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (hβ : β * β = 1)
    (hβ1 : β ≠ 1) {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaPlus 4 2 g) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus 4 K) σ (coordinateQuadPlus_fieldMap 4 σ) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hst : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 2
      f := ⟨⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨γ, hγ⟩ := ((even_orthogonal_involutions_conjugate_into_semilinear_image _ .POmegaPlus
    (Or.inl rfl) 4 f hst).1 K hK (MulEquiv.refl _)).1 β hβ
  have hc' : MulAut.congr γ⁻¹ β = γ⁻¹ * β * γ := MulEquiv.ext fun _ => rfl
  have hβ' : (γ⁻¹ * β * γ) * (γ⁻¹ * β * γ) = 1 := by
    rw [← hc', ← map_mul, hβ, map_one]
  have hβ'1 : γ⁻¹ * β * γ ≠ 1 := by
    intro h
    apply hβ1
    have h1 : γ * (γ⁻¹ * β * γ) * γ⁻¹ = 1 := by rw [h, mul_one, mul_inv_cancel]
    rw [← h1]
    group
  let eF : fixedSubgroup β ≃* fixedSubgroup (γ⁻¹ * β * γ) :=
    (CatLeafProof.fixedSubgroupCongrEquiv γ⁻¹ β).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc'))
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_component_of_mem_image hσ le_rfl hγ hβ' hβ'1
    (CFSG.LocalCores.isComponent_map_mulEquiv eF hD)
    (LieType.CurtisTits.lieModel_of_mulEquiv (D.equivMapOfInjective _ eF.injective) hDm)
  refine ⟨ψ * γ⁻¹, ?_⟩
  rw [← hψ]
  group

end Descent

section Extension

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {n : ℕ}

theorem exists_mulAut_incl_comm_of_mem
    {δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n k))}
    (hδ : δ ∈ matrixProjectiveImage (coordinateQuadPlus n k)) :
    ∃ δ' : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ∀ x, δ' (incl k (isExtension_coordinateQuadPlus n k) x) =
        incl k (isExtension_coordinateQuadPlus n k) (δ x) := by
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ δ).mp hδ
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq k.subtype g.val.right
  obtain ⟨μ, hμ⟩ := g.property
  have hA : ∀ u, coordinateQuadPlus n k (g.val.left.val *ᵥ u) =
      (μ : k) * coordinateQuadPlus n k u := by
    intro u
    have h1 := hμ (coordinateFieldMap (2 * n) g.val.right.symm u)
    rw [coordinateSemilinearMap_apply, ← coordinateQuadPlus_fieldMap] at h1
    have hu : coordinateFieldMap (2 * n) g.val.right
        (coordinateFieldMap (2 * n) g.val.right.symm u) = u := by
      funext i
      simp only [coordinateFieldMap_apply, RingEquiv.apply_symm_apply]
    have hu' : (fun i => g.val.right (coordinateFieldMap (2 * n) g.val.right.symm u i)) = u := by
      funext i
      simp only [coordinateFieldMap_apply, RingEquiv.apply_symm_apply]
    rw [hu, hu'] at h1
    exact h1
  let g' : coordinateSemilinearGroup (2 * n) K := ⟨glIncl k g.val.left, ρ'⟩
  have hg' : g' ∈ similarityPairs (coordinateQuadPlus n K) := by
    refine ⟨Units.map k.subtype.toMonoidHom μ, fun w => ?_⟩
    rw [coordinateSemilinearMap_apply]
    change coordinateQuadPlus n K ((glIncl k g.val.left).val *ᵥ fun i => ρ' (w i)) =
      ((μ : k) : K) * ρ' (coordinateQuadPlus n K w)
    rw [coordinateQuadPlus_glIncl hA, ← coordinateQuadPlus_fieldMap]
    rfl
  refine ⟨matrixProjectiveConjugation _ ⟨g', hg'⟩, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
  rw [← hg, matrixProjectiveConjugation_mk, incl_mk, incl_mk, matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val, inclHom_val, inclHom_val, matrixDerivedConjugation_val]
  have hent : glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) =
      glIncl k (glFieldAut (Fin (2 * n)) k g.val.right y.val) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change ρ' (k.subtype (y.val.val i j)) = k.subtype (g.val.right (y.val.val i j))
    exact hρ' _
  change glIncl k g.val.left * glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) *
      (glIncl k g.val.left)⁻¹ = _
  rw [hent, map_mul, map_mul, map_inv]

end Extension

end CFSG.SeitzReduction.OmegaPilot
