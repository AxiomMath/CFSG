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
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.E7Pilot

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_conj_eq_fieldAutT_of_component {σ : K ≃+* K} (hσ : orderOf σ = 2) (hn : 5 ≤ n)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hβ : β * β = 1)
    (hβ1 : β ≠ 1) {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaPlus n 2 g) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldMap n σ) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
    exact Subgroup.mem_top β
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

end Descent

section Normalize

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem exists_mulEquiv_comp_eq_incl {σ : F ≃+* F} (hσ : orderOf σ = 2) {k : Subfield F}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) (hm : 5 ≤ m)
    {Kc : Type} [Group Kc] (ψ₀ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus m F))
    {τ : MulAut Kc} (hτ : τ * τ = 1) (hτout : τ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    {D' : Subgroup (fixedSubgroup τ)} (hD' : CFSG.IsComponent D') {g : ℕ}
    (hD'm : LieModel D' .POmegaPlus m 2 g)
    {A : Type} [Group A] (ε : A →* Kc) (hε : Function.Injective ε)
    (hεr : ε.range = D'.map (fixedSubgroup τ).subtype)
    (j : A ≃* matrixProjectiveDerived (coordinateQuadPlus m k)) :
    ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus m F),
      ∀ a, ψ (ε a) = incl k (isExtension_coordinateQuadPlus m k) (j a) := by
  have hext := isExtension_coordinateQuadPlus m k
  set β : MulAut (matrixProjectiveDerived (coordinateQuadPlus m F)) :=
    MulAut.congr ψ₀ τ with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hτout
    have hτ1 : τ = 1 := (MulAut.congr ψ₀).injective (by rw [← hβdef, h, map_one])
    exact ⟨1, by rw [map_one, hτ1]⟩
  have hfix : fixedSubgroup β = (fixedSubgroup τ).map ψ₀.toMonoidHom :=
    ExcSelector.fixedSubgroup_congr ψ₀ τ
  let Φ : fixedSubgroup τ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ).equivMapOfInjective ψ₀.toMonoidHom ψ₀.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  have hD'' : CFSG.IsComponent (D'.map Φ.toMonoidHom) := CatLeaf.isComponent_map_mulEquiv Φ hD'
  have hD''m : LieModel (D'.map Φ.toMonoidHom) .POmegaPlus m 2 g :=
    LieType.CurtisTits.lieModel_of_mulEquiv (D'.equivMapOfInjective Φ.toMonoidHom Φ.injective)
      hD'm
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_component hσ hm hβ hβ1 hD'' hD''m
  set σs := fieldAutT (coordinateQuadPlus m F) σ (coordinateQuadPlus_fieldMap m σ) with hσs
  set ψ₁ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus m F) := ψ₀.trans ψ with hψ₁
  have hσψ : ∀ x, σs (ψ x) = ψ (β x) := by
    intro x
    have h1 := congrArg (fun γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus m F)) =>
      γ (ψ x)) hψ
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    exact h1.symm
  have hfixε : ∀ a, ψ₁ (ε a) ∈ fixedSubgroup σs := by
    intro a
    obtain ⟨d, -, hda⟩ : ε a ∈ D'.map (fixedSubgroup τ).subtype := hεr ▸ ⟨a, rfl⟩
    have hτd : τ (ε a) = ε a := by
      rw [← hda]
      exact d.2
    change σs (ψ (ψ₀ (ε a))) = ψ (ψ₀ (ε a))
    rw [hσψ]
    congr 1
    change ψ₀ (τ (ψ₀.symm (ψ₀ (ε a)))) = ψ₀ (ε a)
    rw [MulEquiv.symm_apply_apply, hτd]
  set ε' : matrixProjectiveDerived (coordinateQuadPlus m k) →*
      matrixProjectiveDerived (coordinateQuadPlus m F) :=
    (ψ₁.toMonoidHom.comp ε).comp j.symm.toMonoidHom with hε'
  have hε'inj : Function.Injective ε' := ψ₁.injective.comp (hε.comp j.symm.injective)
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    commutator_range_of_commutator_top _ (commutator_top_coordinatePlus (by omega))
  obtain ⟨hQ, -⟩ := regular_coordinateQuadPlus m F (by omega)
  have hQne : ∃ v, coordinateQuadPlus m F v ≠ 0 :=
    exists_ne_zero_of_nondeg (by omega : 0 < 2 * m) hQ
  have hcore := perfectCore_fixedSubgroup_fieldAutT (coordinateQuadPlus_fieldMap m σ) hσk hext
    hQne hJ
  have hperf : ⁅ε'.range, ε'.range⁆ = ε'.range :=
    commutator_range_of_commutator_top _ (commutator_top_coordinatePlus (by omega))
  have hle : ε'.range ≤ subfieldDerivedImage k hext := by
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hperf
    rintro _ ⟨x, rfl⟩
    exact hfixε (j.symm x)
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  have hrange : ε'.range = (incl k hext).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hε'inj).toEquiv]
  let δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus m k)) :=
    ((MonoidHom.ofInjective hε'inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hιinj).symm
  have hδ : ∀ x, incl k hext (δ x) = ε' x := by
    intro x
    have h1 := (MonoidHom.ofInjective hιinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε'inj x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := exists_mulAut_incl_comm hm δ⁻¹
  refine ⟨ψ₁.trans δ', fun a => ?_⟩
  have h3 : ψ₁ (ε a) = ε' (j a) := by
    rw [hε']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, h3, ← hδ, hδ', MulAut.inv_apply, MulEquiv.symm_apply_apply]

end Normalize

end CFSG.SeitzReduction.OmegaPilot
