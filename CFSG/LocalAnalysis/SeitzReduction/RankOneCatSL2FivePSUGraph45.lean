module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FivePSUBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSUGraph
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListL45

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

section Graph


theorem oddFiveU45GraphInput_holds : OddFiveU45GraphInput := by
  intro n K _ f h hn4 hf1 A φ hφ hA hF
  subst hn4
  subst hf1
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd 5 := by decide
  have : Fact (5 : ℕ).Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC (by norm_num) _).mp hx2
  have hmapA : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin 4) K) * glAut φ (A : GL (Fin 4) K) =
        GeneralLinearGroup.scalar (Fin 4) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set Z := normOneScalars h (gramSU h (idGram K 4)) 4 with hZdef
  set ψ : MulAut (gramSU h (idGram K 4)) :=
    primeFormConjSU h (idGram K 4) A * primeFormFieldSU h hC φ with hψdef
  have hinv : Z.map ψ.toMonoidHom = Z := by
    have e1 : ψ.toMonoidHom = (primeFormConjSU h (idGram K 4) A).toMonoidHom.comp
        (primeFormFieldSU h hC φ).toMonoidHom := rfl
    rw [e1, ← Subgroup.map_map, map_normOneScalars_field, map_normOneScalars_conj]
  have hZc : Z ≤ center (gramSU h (idGram K 4)) := normOneScalars_le_center h _ 4
  have heq : primeFormPsi h hC ⟨A, φ⟩ = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : primeFormP h (idGram K 4))) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk, primeFormPsi_apply, MulAut.mul_apply]
      change primeFormConjAut h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
      rw [primeFormFieldAut_mk, primeFormConjAut_mk]
      rfl
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ :=
    CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  let φS : gramSU h (idGram K 4) →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 4) K ≃*
      LinearMap.GeneralLinearGroup K (Fin 4 → K)).toMonoidHom.comp
        (gramSU h (idGram K 4)).subtype
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hxy)
  have hfixg : ∀ g : gramSU h (idGram K 4), g ∈ fixedSubgroup ψ ↔
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
    intro g
    change ψ g = g ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin 4) K) * glAut φ (g : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ = g ↔ _
    rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut]
    have hmap : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := Matrix.ext fun i j => hφ _
    rw [hmap]
    exact eq_comm
  have htoLin : ∀ (g : GL (Fin 4) K) (v : Fin 4 → K),
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
        (Fin 4 → K) →ₗ[K] (Fin 4 → K)) v = (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v := fun g v => by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hmap : (fixedSubgroup ψ).map φS =
      commutingUnitary (idForm h 4) τ₀ ⊓ sesqSpecialUnitaryGroup (idForm h 4) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hS : φS g ∈ sesqSpecialUnitaryGroup (idForm h 4) :=
        (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K 4) g).mpr g.2
      refine Subgroup.mem_inf.mpr ⟨⟨sesqSpecialUnitaryGroup_le _ hS, fun v => ?_⟩, hS⟩
      change ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) :
          LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] (Fin 4 → K))
            (τ₀ v) = τ₀ (((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) :
              LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) v)
      rw [htoLin, htoLin]
      exact (CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mpr ((hfixg g).mp hg) v
    · intro hy
      obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
      set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K 4) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hyS
      refine ⟨⟨g, hg⟩, (hfixg _).mpr
        ((CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mp
        fun v => ?_), hgy⟩
      have h1 := hyC.2 v
      rw [← hgy, htoLin, htoLin] at h1
      exact h1
  have hnormal : ((commutingUnitary (idForm h 4) τ₀ ⊓
      sesqSpecialUnitaryGroup (idForm h 4)).subgroupOf (commutingUnitary (idForm h 4) τ₀)).Normal
      := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    rw [sesqSpecialUnitaryGroup] at hxS ⊢
    obtain ⟨hxU, hxD⟩ := Subgroup.mem_inf.mp hxS
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        mul_mem (mul_mem g.2.1 hxU) (inv_mem g.2.1)
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (MonoidHom.normal_ker _).conj_mem _ hxD (g : LinearMap.GeneralLinearGroup K (Fin 4 → K))
  obtain ⟨L, hL, hLm⟩ := hF.1
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective eF.toMonoidHom eF.injective) hLm
  obtain ⟨N, hN, ⟨eN⟩⟩ := FiveList.exists_component_of_map_inf Z hZc ψ hinv φS hφS _ _ hmap
    hnormal hL'
  have hNm : LieModel (N ⧸ center N) .PSL 2 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv eN hL'm
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; omega) (idForm_isSymm h 4) (idForm_separatingLeft h 4)
    τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 5 ^ 1 := h.card_fixedField
  have hdimW : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  rcases hμ1 with hμ1 | hμ1
  ·
    obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp2 h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    let Ψ := Φ.trans (MulEquiv.subgroupCongr
      (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    have hN' := LocalCores.isComponent_map_mulEquiv Ψ hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hNm
    by_cases hS : ∃ S : Submodule h.fixedField (conjFixed h ((b : K) • τ₀)),
        Module.finrank h.fixedField S = 2 ∧
          ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
    ·
      obtain ⟨S, hSd, hSQ⟩ := hS
      obtain ⟨-, e, -, -, -⟩ := CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
        (CatalogueBOrthogonalDescent.originalQuadratic B') hQ hdimW S hSd hSQ
      have h7 : 2 ^ 7 ∣ Nat.card (commutingUnitary (idForm h 4) τ₀) := by
        rw [Nat.card_congr (Ψ.trans e).toEquiv]
        exact FiveList.two_pow_seven_dvd_card_det (by rw [hkc, pow_one])
      apply hF.not_dvd
      have hcard : Nat.card (fixedSubgroup (primeFormPsi h hC ⟨A, φ⟩)) =
          Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
        rw [heq]
      rw [hcard]
      have hCS : Nat.card (commutingUnitary (idForm h 4) τ₀) = Nat.card (fixedSubgroup ψ) *
          (sesqSpecialUnitaryGroup (idForm h 4)).relIndex (commutingUnitary (idForm h 4) τ₀) := by
        have h1 := Subgroup.card_mul_index ((sesqSpecialUnitaryGroup (idForm h 4)).subgroupOf
          (commutingUnitary (idForm h 4) τ₀))
        have h2 : Nat.card ((sesqSpecialUnitaryGroup (idForm h 4)).subgroupOf
            (commutingUnitary (idForm h 4) τ₀)) = Nat.card (fixedSubgroup ψ) := by
          rw [← Subgroup.inf_subgroupOf_right (sesqSpecialUnitaryGroup (idForm h 4))
              (commutingUnitary (idForm h 4) τ₀),
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, ← hmap,
            Subgroup.card_map_of_injective hφS]
        rw [← h1, h2]
        rfl
      have hidx := FiveList.relIndex_sesqSpecialUnitaryGroup_dvd h (idForm_isSymm h 4)
        (idForm_separatingLeft h 4) (by rw [Module.finrank_fin_fun]; omega)
        (G₀ := commutingUnitary (idForm h 4) τ₀) fun g hg => hg.1
      exact FiveList.thirty_two_dvd_of_two_pow_seven_dvd (hCS ▸ h7) hidx
        (FiveList.card_fixed_dvd_card_mul Z ψ hinv)
        (FiveList.card_normOneScalars_dvd_six h (by norm_num) (by norm_num))
    ·
      exact false_of_orth_nonsplit_four le_rfl hkc
        (CatalogueBOrthogonalDescent.originalQuadratic B') hQ hdimW hS hN' hN'm
  ·
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B' halt hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B' halt hnd hdm
    let Ψ := Φ.trans eS
    have hN' := LocalCores.isComponent_map_mulEquiv Ψ hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hNm
    obtain ⟨hadmS, hmodS⟩ := FiveList.lieModel_of_isComponent_statedSp h.prime hp2 le_rfl hkc
      (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hN'm hp2 hadmS hmodS
    exact absurd h1 (by decide)

end Graph

end CFSG.SeitzReduction.RankOne
