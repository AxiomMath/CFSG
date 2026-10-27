module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSUGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenL47

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

namespace SevenList

theorem det_mul_self_eq_one_of_mem_commutingUnitary {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (A : GL (Fin n) K)
    {y : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hy : y ∈ commutingUnitary (idForm h n)
      (semilinearMatrixMap h (A : Matrix (Fin n) (Fin n) K))) :
    LinearMap.det (y : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.det (y : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
  set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
  have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
  have hdet : LinearMap.det (y : (Fin n → K) →ₗ[K] (Fin n → K)) =
      (g : Matrix (Fin n) (Fin n) K).det := by
    rw [← hgy, Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']
  have hU : g ∈ primeFormUnitary h (idGram K n) :=
    (toLin_mem_sesqUnitaryGroup_iff g).mp (hgy ▸ hy.1)
  rw [mem_primeFormUnitary] at hU
  have h1 := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h1
  have hc : (g : Matrix (Fin n) (Fin n) K) * A = A * (g : Matrix (Fin n) (Fin n) K).map h.bar := by
    refine (CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mp fun v => ?_
    have h2 := hy.2 v
    rw [← hgy, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply] at h2
    exact h2
  have h2 := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
  have hA0 : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have h3 : (g : Matrix (Fin n) (Fin n) K).det = h.bar (g : Matrix (Fin n) (Fin n) K).det := by
    have := h2
    rw [mul_comm ((A : Matrix (Fin n) (Fin n) K).det)] at this
    exact mul_right_cancel₀ hA0 this
  have hI : (idGram K n).det = 1 := by simp [idGram]
  rw [hI, mul_one, ← h3] at h1
  rw [hdet]
  exact h1

theorem relIndex_commutingUnitary_dvd_two {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (A : GL (Fin n) K) :
    (sesqSpecialUnitaryGroup (idForm h n)).relIndex
      (commutingUnitary (idForm h n) (semilinearMatrixMap h (A : Matrix (Fin n) (Fin n) K))) ∣
        2 := by
  have : Finite K := h.finite
  set G₀ := commutingUnitary (idForm h n) (semilinearMatrixMap h (A : Matrix (Fin n) (Fin n) K))
  let d : G₀ →* Kˣ :=
    (Units.map (LinearMap.det : ((Fin n → K) →ₗ[K] (Fin n → K)) →* K)).comp G₀.subtype
  have hd : ∀ x : G₀, ((d x : Kˣ) : K) =
      LinearMap.det (((x : LinearMap.GeneralLinearGroup K (Fin n → K))) :
        (Fin n → K) →ₗ[K] (Fin n → K)) := fun x => rfl
  have hker : d.ker = (sesqSpecialUnitaryGroup (idForm h n)).subgroupOf G₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup, Units.ext_iff,
      hd, Units.val_one]
    exact ⟨fun hx => ⟨x.2.1, hx⟩, fun hx => hx.2⟩
  have hsq : ∀ x : G₀, d x * d x = 1 := fun x => Units.ext (by
    rw [Units.val_mul, hd, Units.val_one]
    exact det_mul_self_eq_one_of_mem_commutingUnitary h A x.2)
  have hrange : Nat.card d.range ≤ 2 := by
    have hle : d.range ≤ Subgroup.zpowers (-1 : Kˣ) := by
      rintro u ⟨x, rfl⟩
      have h1 := congrArg Units.val (hsq x)
      rw [Units.val_mul, Units.val_one] at h1
      rcases mul_self_eq_one_iff.mp h1 with h2 | h2
      · rw [show d x = 1 from Units.ext h2]
        exact one_mem _
      · rw [show d x = -1 from Units.ext (by rw [h2, Units.val_neg, Units.val_one])]
        exact Subgroup.mem_zpowers _
    calc Nat.card d.range ≤ Nat.card (Subgroup.zpowers (-1 : Kˣ)) := Subgroup.card_le_of_le hle
      _ = orderOf (-1 : Kˣ) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [neg_one_sq])
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact RankOne.FiveList.card_dvd_two_of_le hrange

end SevenList


section Graph


theorem lFiveSevenU47GraphInput_holds : LFiveSevenU47GraphInput := by
  intro n K _ f h hn4 hf1 A φ hφ hA hF
  subst hn4
  subst hf1
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd 7 := by decide
  have : Fact (7 : ℕ).Prime := ⟨h.prime⟩
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
  have hL'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective eF.toMonoidHom eF.injective) hLm
  obtain ⟨N, hN, ⟨eN⟩⟩ := RankOne.FiveList.exists_component_of_map_inf Z hZc ψ hinv φS hφS _ _ hmap
    hnormal hL'
  have hNm : LieModel (N ⧸ center N) .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eN hL'm
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; omega) (idForm_isSymm h 4) (idForm_separatingLeft h 4)
    τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 7 ^ 1 := h.card_fixedField
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
    have hN'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hNm
    by_cases hS : ∃ S : Submodule h.fixedField (conjFixed h ((b : K) • τ₀)),
        Module.finrank h.fixedField S = 2 ∧
          ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
    ·
      obtain ⟨S, hSd, hSQ⟩ := hS
      obtain ⟨-, e, -, -, -⟩ := CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
        (CatalogueBOrthogonalDescent.originalQuadratic B') hQ hdimW S hSd hSQ
      have h9 : 2 ^ 9 ∣ Nat.card (commutingUnitary (idForm h 4) τ₀) := by
        rw [Nat.card_congr (Ψ.trans e).toEquiv]
        exact SevenList.two_pow_nine_dvd_card_det (by rw [hkc, pow_one])
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
      have hidx : (sesqSpecialUnitaryGroup (idForm h 4)).relIndex
          (commutingUnitary (idForm h 4) τ₀) ∣ 2 ^ 1 * 1 := by
        rw [show 2 ^ 1 * 1 = 2 by norm_num]
        exact SevenList.relIndex_commutingUnitary_dvd_two h (A : GL (Fin 4) K)
      have h9' : 2 ^ (8 + 1) ∣ Nat.card (fixedSubgroup ψ) *
          (sesqSpecialUnitaryGroup (idForm h 4)).relIndex (commutingUnitary (idForm h 4) τ₀) :=
        hCS ▸ h9
      have h8 := SevenList.two_pow_dvd_of_dvd_mul_of_dvd h9' hidx (by decide)
      have hZ : Nat.card Z ∣ 2 ^ 2 * 1 := by
        rw [hZdef, RankThree.Classical.card_normOneScalars_one h (by norm_num)]
        decide
      have h8' : 2 ^ (6 + 2) ∣ Nat.card (fixedSubgroup
          (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) * Nat.card Z := by
        rw [mul_comm]
        exact h8.trans (RankOne.FiveList.card_fixed_dvd_card_mul Z ψ hinv)
      exact (by norm_num : 64 ∣ 2 ^ 6).trans
        (SevenList.two_pow_dvd_of_dvd_mul_of_dvd h8' hZ (by decide))
    ·
      exact SevenList.false_of_orth_nonsplit_four le_rfl hkc
        (CatalogueBOrthogonalDescent.originalQuadratic B') hQ hdimW hS hN' hN'm
  ·
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B' halt hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B' halt hnd hdm
    let Ψ := Φ.trans eS
    have hN' := LocalCores.isComponent_map_mulEquiv Ψ hN
    have hN'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hNm
    obtain ⟨hadmS, hmodS⟩ :=
      RankOne.FiveList.lieModel_of_isComponent_statedSp h.prime hp2 le_rfl hkc (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hN'm hp2 hadmS hmodS
    exact absurd h1 (by decide)

end Graph

section Holds


theorem lFiveSevenListFamilyInput_PSU_holds : LFiveSevenListFamilyInput .PSU :=
  lFiveSevenListFamilyInput_PSU_of_classes lFiveSevenPSUInnerInput_holds
    (lFiveSevenPSUGraphInput_of_U47 lFiveSevenU47GraphInput_holds)

theorem lFiveSevenRankFamilyInput_PSU_holds : LFiveSevenRankFamilyInput .PSU :=
  lFiveSevenRankFamilyInput_of_list lFiveSevenListFamilyInput_PSU_holds

end Holds

end CFSG.SeitzReduction.LinearPilot
