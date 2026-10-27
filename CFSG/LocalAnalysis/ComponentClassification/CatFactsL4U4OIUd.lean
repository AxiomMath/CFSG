module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem descent_model (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {c : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = c • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y
      (FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ Subgroup.center Y)
    (hXm : Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 2 p (2 * f)) :
    c = 1 ∧ finrank h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)) = 4 ∧
    ∃ B' : LinearMap.BilinForm h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)),
      (∀ v w, (B' v w : K) = stdHermForm h 4 v w) ∧ B'.IsSymm ∧
      ∃ (δ : h.fixedFieldˣ) (_ : ¬ IsSquare (δ : h.fixedField)) (d : h.fixedFieldˣ)
        (ψW : fixW h (A : Matrix (Fin 4) (Fin 4) K) ≃ₗ[h.fixedField]
          hermitianSubmodule (δ : h.fixedField)),
        (∀ w, B' w w / 2 = (d : h.fixedField) * hermitianForm (δ : h.fixedField) (ψW w)) ∧
        ∀ (u : sesqUnitaryGroup (stdHermForm h 4))
          (_ : u ∈ FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)),
          u ∈ Y ↔ ∃ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
            ∀ w : fixW h (A : Matrix (Fin 4) (Fin 4) K),
              unitaryOp u (w : Fin 4 → K) =
                ((ψW.symm (rowOAction δ g (ψW w)) : fixW h (A : Matrix (Fin 4) (Fin 4) K)) :
                  Fin 4 → K) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := StabU.antiunitaryMap_bijective h A
  have hτ₀B := StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hμ : ∀ v, antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 c hz0 : Kˣ) : K) • v :=
    StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 c hz0) hμ
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp2 h1
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    exfalso
    obtain ⟨-, hfinW, -, -, hB2⟩ := hall b t hb ht
    have : Module.Finite h.fixedField
        (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
      finite_conjFixed
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    let F := (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ
    have hq := CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun]) hKodd
    have hYtop := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq
      (isComponent_map_of_isComponent F hY₁)
    obtain ⟨m, hd, ⟨eSp⟩⟩ :=
      CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B' halt hnd
    have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m)
      (K := h.fixedField)
    let τ : StatedSp m h.fixedField ≃* Y.subgroupOf
        (FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)) :=
      (((MulEquiv.subgroupCongr heq).trans eSp.symm).trans
        ((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv).symm).trans
          ((Y.subgroupOf _).equivMapOfInjective F.toMonoidHom F.injective).symm
    have hm : 2 ≤ m := by rw [hfinW, Module.finrank_fin_fun] at hd; omega
    have hns := (OddSelector.not_small_source_of_sp_cover hm h.prime hp2 h.one_le hK
      ((σ.comp eY.toMonoidHom).comp τ.toMonoidHom)
      (OddClassSelector.ker_comp_le_center τ.toMonoidHom τ.injective _ hσ₁k)).1 p (2 * f) hp2
    exact hns (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hXm)
  have hc1 : c = 1 := by
    have := congrArg Units.val hμ1
    simpa using this
  refine ⟨hc1, ?_⟩
  have hb1 : h.norm ((1 : Kˣ) : K) = (((Units.mk0 c hz0)⁻¹ : Kˣ) : K) := by
    rw [hμ1, inv_one, Units.val_one, UnitaryFieldData.norm, map_one, one_mul]
  obtain ⟨-, hfinW, -, hB1, -⟩ := hall 1 t hb1 ht
  have : Module.Finite h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)) := finite_conjFixed
  have hdim : finrank h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  refine ⟨hdim, ?_⟩
  obtain ⟨B', hB'v, hsym, hnd, Φ, hΦ⟩ := hB1 hμ1
  refine ⟨B', hB'v, hsym, ?_⟩
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  let Φ' : FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B') :=
    (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  by_cases hsplit : ∃ S : Submodule h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)),
      finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  · exfalso
    obtain ⟨-, ⟨eSL⟩⟩ :=
      GSThmB.Catalog7L4EU.component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
    let eYY' : Y ≃* (Y.subgroupOf _).map Φ'.toMonoidHom :=
      eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
    have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
    obtain ⟨eP⟩ := GSThmB.Catalog7L4EU.center_quotient_equiv_of_sl σ hσs hσk (eYY'.trans eSL)
    exact false_of_psl2_fixed h hp2 hXm eP
  obtain ⟨-, -, -, -, hnon, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
    _ hQ' (Or.inl ⟨hKodd, Or.inr (Or.inl hdim)⟩)
  obtain ⟨δ, hδ, d, ψW, e, hψ, he, hc, hquasi⟩ := hnon hKodd hdim hsplit
  refine ⟨δ, hδ, d, ψW, fun w => ?_, ?_⟩
  · have := hψ w
    rw [CatalogueBOrthogonalDescent.originalQuadratic_apply] at this
    exact this
  intro u hu
  have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
  have key := mem_iff_of_model (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hKodd) ψW e he hc
    Φ' hYeq ⟨u, hu⟩
  have hΦ'w : ∀ w : fixW h (A : Matrix (Fin 4) (Fin 4) K),
      (((Φ' ⟨u, hu⟩).val w : fixW h (A : Matrix (Fin 4) (Fin 4) K)) : Fin 4 → K) =
        unitaryOp u (w : Fin 4 → K) := fun w => hΦ _ w
  rw [show u ∈ Y ↔ (⟨u, hu⟩ : FixedCommutingProduct.fixedSubgroup
      (GSThmB.Catalog7L4EU.antiConjA h hAu)) ∈ Y.subgroupOf _ from Iff.rfl,
    key]
  refine exists_congr fun g => forall_congr' fun w => ?_
  rw [Subtype.ext_iff, hΦ'w w]

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
