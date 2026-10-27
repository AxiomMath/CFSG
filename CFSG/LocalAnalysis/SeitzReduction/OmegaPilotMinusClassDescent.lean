module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYDescent
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYExt

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
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)
open CFSG.GroupTheory.WeirSylow (binForm binForm_isometry quadMinusIsometry)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed
  isExtension_coordinateQuadMinus false_of_lieModel_omegaPlus_omegaMinus
  false_of_component_of_statedSp_omega false_of_isComponent_fixedSubgroup_one
  exists_mulEquiv_conj_fieldAutT_of_minus fieldAutT_congr_right AutExtensionComm
  autExtensionComm_incl_minus)
open CFSG.Quasithin (perfectCore)

theorem commutator_top_coordinateMinus {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 4 ≤ n)
    {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ⁅(⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c))),
      (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)))⁆ = ⊤ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n k b c hn hirr
  obtain ⟨hs, hnab⟩ := matrix_simple_nonabelian (by omega : 0 < 2 * n) hQ hT
  exact E7Pilot.commutator_top_of_isSimpleGroup hnab

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_mulEquiv_congr_eq_fieldAutT_minus {σ : K ≃+* K} (hσ : orderOf σ = 2) (hn : 5 ≤ n)
    {b c : K} (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hβ : β * β = 1)
    {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {m g : ℕ}
    (hDm : LieModel D .POmegaMinus m 2 g) :
    ∃ Θ : matrixProjectiveDerived (coordinateQuadPlus n K) ≃*
        matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus n K (by omega) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hDp := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
    exact Subgroup.mem_top β
  have hβ1 : β ≠ 1 := by
    rintro rfl
    obtain ⟨hs, -⟩ := matrix_simple_nonabelian (by omega : 0 < 2 * n) hQ hT
    exact false_of_isComponent_fixedSubgroup_one
      (E7Pilot.lieModel_coordinatePlus hf hK (by omega)) hD hDm
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
      (E7Pilot.statedClassicalModel_coordinatePlus (n := n) hf hK (by omega))
    have heq : fixedSubgroup β = centralizer ({z} : Set _) := by
      rw [← hz]
      exact E7Pilot.fixedSubgroup_mulAut_conj_eq z
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
      exact false_of_component_of_statedSp_omega hK hf (by omega : 3 ≤ n - 1)
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
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨g', hg', hk'⟩ :=
    F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 n
      (by omega) hdim with ⟨b', hb'⟩ | ⟨β', γ', -, hroot, b', hb'⟩
  ·
    exfalso
    obtain ⟨eP⟩ := E7Pilot.nonempty_mulEquiv_pairDescentDerived hf hK (by omega) hQ hT hE hβim
      hβ2 hinn hS hSβ hσ1 hDp
    have hreg := regular_coordinateQuadPlus n (descentField S.val.right) (by omega)
    obtain ⟨eM⟩ := E7Pilot.nonempty_derived_mulEquiv_of_isometry hg' hk' (by omega) _
      ((plusBasisIsometry b' hb').trans (coordinatePlusIsometry n (descentField S.val.right)))
      hreg.1 hreg.2 (commutator_coordinateQuadPlus n (descentField S.val.right) (by omega))
    exact false_of_lieModel_omegaPlus_omegaMinus
      (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eM).symm
        (E7Pilot.lieModel_coordinatePlus hg' hk' (by omega))) hDm
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
        (quadMinus n (descentField S.val.right) ⟨b, hbk⟩ ⟨c, hck⟩) :=
      (minusBasisIsometry b' hb').trans ((quadMinusIsometry n β' γ').trans
        (((QuadraticMap.IsometryEquiv.refl _).prod ι).trans
          (quadMinusIsometry n _ _).symm))
    have hQ'σ : ∀ v, coordinateQuadMinus n K (by omega) b c
        (coordinateFieldMap (2 * n) S.val.right v) =
          S.val.right (coordinateQuadMinus n K (by omega) b c v) := by
      rw [← hσS]
      exact coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc
    obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_conj_fieldAutT_of_minus (K := K) (n := n) (by omega) hQ
      hS hσσ hσ1 hTT ⟨b, hbk⟩ ⟨c, hck⟩ φ hQ'σ
    refine ⟨Θ, ?_⟩
    rw [fieldAutT_congr_right _ hσS _ hQ'σ]
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    change Θ (β (Θ.symm (Θ y))) = _
    rw [MulEquiv.symm_apply_apply, ← hSβ]
    exact hΘ y

end Descent

section Normalize

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem exists_mulEquiv_comp_eq_incl_minus {σ : F ≃+* F} (hσ : orderOf σ = 2) {k : Subfield F}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) (hm : 5 ≤ m) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {Kc : Type} [Group Kc] (ψ₀ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus m F))
    {τ : MulAut Kc} (hτ : τ * τ = 1)
    {D' : Subgroup (fixedSubgroup τ)} (hD' : CFSG.IsComponent D') {g : ℕ}
    (hD'm : LieModel D' .POmegaMinus m 2 g)
    {A : Type} [Group A] (ε : A →* Kc) (hε : Function.Injective ε)
    (hεr : ε.range = D'.map (fixedSubgroup τ).subtype)
    (j : A ≃* matrixProjectiveDerived (coordinateQuadMinus m k (by omega) b c)) :
    ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadMinus m F (by omega) (b : F) (c : F)),
      (∀ a, ψ (ε a) = incl k (isExtension_coordinateQuadMinus k (by omega) b c) (j a)) ∧
      MulAut.congr ψ τ = fieldAutT (coordinateQuadMinus m F (by omega) (b : F) (c : F)) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) ((hσk b).1 b.2) ((hσk c).1 c.2)) := by
  have hm1 : 1 ≤ m := by omega
  have hext := isExtension_coordinateQuadMinus k hm1 b c
  have hb : σ (b : F) = b := (hσk b).1 b.2
  have hc : σ (c : F) = c := (hσk c).1 c.2
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + (b : F) * s + (c : F) ≠ 0 := by
    intro s hs h0
    apply hirr ⟨s, (hσk s).2 hs⟩
    apply Subtype.ext
    simpa using h0
  have hQσ := coordinateQuadMinus_fieldMap_of_fixed (n := m) hm1 hb hc
  set σs := fieldAutT (coordinateQuadMinus m F hm1 (b : F) (c : F)) σ hQσ with hσs
  set β : MulAut (matrixProjectiveDerived (coordinateQuadPlus m F)) := MulAut.congr ψ₀ τ
    with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hfix : fixedSubgroup β = (fixedSubgroup τ).map ψ₀.toMonoidHom :=
    ExcSelector.fixedSubgroup_congr ψ₀ τ
  let Φ : fixedSubgroup τ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ).equivMapOfInjective ψ₀.toMonoidHom ψ₀.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  have hD'' : CFSG.IsComponent (D'.map Φ.toMonoidHom) := CatLeaf.isComponent_map_mulEquiv Φ hD'
  have hD''m : LieModel (D'.map Φ.toMonoidHom) .POmegaMinus m 2 g :=
    LieType.CurtisTits.lieModel_of_mulEquiv (D'.equivMapOfInjective Φ.toMonoidHom Φ.injective)
      hD'm
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_congr_eq_fieldAutT_minus hσ hm hb hc hirrF hβ hD'' hD''m
  set ψ₁ : Kc ≃* matrixProjectiveDerived (coordinateQuadMinus m F hm1 (b : F) (c : F)) :=
    ψ₀.trans Θ with hψ₁
  have hψ₁τ : MulAut.congr ψ₁ τ = σs := by
    have h1 : MulAut.congr ψ₁ τ = MulAut.congr Θ β := MulEquiv.ext fun _ => rfl
    rw [h1, hΘ]
  have hσψ : ∀ x, ψ₁ (τ x) = σs (ψ₁ x) := fun x => by
    rw [← hψ₁τ]
    change ψ₁ (τ x) = ψ₁ (τ (ψ₁.symm (ψ₁ x)))
    rw [MulEquiv.symm_apply_apply]
  have hfixε : ∀ a, ψ₁ (ε a) ∈ fixedSubgroup σs := by
    intro a
    obtain ⟨d, -, hda⟩ : ε a ∈ D'.map (fixedSubgroup τ).subtype := hεr ▸ ⟨a, rfl⟩
    have hτd : τ (ε a) = ε a := by
      rw [← hda]
      exact d.2
    change σs (ψ₁ (ε a)) = ψ₁ (ε a)
    rw [← hσψ, hτd]
  set ε' : matrixProjectiveDerived (coordinateQuadMinus m k hm1 b c) →*
      matrixProjectiveDerived (coordinateQuadMinus m F hm1 (b : F) (c : F)) :=
    (ψ₁.toMonoidHom.comp ε).comp j.symm.toMonoidHom with hε'
  have hε'inj : Function.Injective ε' := ψ₁.injective.comp (hε.comp j.symm.injective)
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
  obtain ⟨hQk, -⟩ := regular_coordinateQuadMinus m k b c (by omega) hirr
  have hQne : ∃ v, coordinateQuadMinus m F hm1 (b : F) (c : F) v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne_zero_of_nondeg (by omega : 0 < 2 * m) hQk
    refine ⟨vecIncl k v, ?_⟩
    rw [hext v]
    exact fun h => hv (Subtype.ext h)
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT hQσ hσk hext hQne hJ
  have hperf : ⁅ε'.range, ε'.range⁆ = ε'.range :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
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
  let δ : MulAut (matrixProjectiveDerived (coordinateQuadMinus m k hm1 b c)) :=
    ((MonoidHom.ofInjective hε'inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hιinj).symm
  have hδ : ∀ x, incl k hext (δ x) = ε' x := by
    intro x
    have h1 := (MonoidHom.ofInjective hιinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε'inj x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδ'c⟩ := autExtensionComm_incl_minus (n := m) (by omega) hσk b c hirr hQσ δ⁻¹
  refine ⟨ψ₁.trans δ', fun a => ?_, ?_⟩
  · have h3 : ψ₁ (ε a) = ε' (j a) := by
      rw [hε']
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [MulEquiv.trans_apply, h3, ← hδ, hδ', MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · have h4 : MulAut.congr (ψ₁.trans δ') τ = δ' * MulAut.congr ψ₁ τ * δ'⁻¹ :=
      MulEquiv.ext fun _ => rfl
    rw [h4, hψ₁τ, hδ'c, mul_assoc, mul_inv_cancel, mul_one]

end Normalize

end CFSG.SeitzReduction.OmegaPilot
