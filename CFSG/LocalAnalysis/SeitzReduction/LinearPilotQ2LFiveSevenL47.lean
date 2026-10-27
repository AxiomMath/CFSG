module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenOrth
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListL45

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace SevenList

open CatalogueBOrthogonalFourSplit

theorem card_range_rho_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    Nat.card (rho (K := K)).range = 112896 := by
  have h1 := RankOne.FiveList.card_equalDeterminants_mul K
  have h2 := Subgroup.card_ker_mul_card_range (rho (K := K))
  rw [RankOne.FiveList.card_ker_rho] at h2
  have hU : Nat.card Kˣ = 6 := by rw [Nat.card_units, hK]
  rw [hU, card_GL_two_seven hK] at h1
  rw [hU] at h2
  omega

theorem two_pow_nine_dvd_card_det {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    2 ^ 9 ∣ Nat.card (DeterminantIsometries K) := by
  set H := (rho (K := K)).range with hHdef
  have hH := card_range_rho_seven hK
  set N := normalizer (H : Set (DeterminantIsometries K)) with hNdef
  have htauN : tau ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact RankOne.FiveList.tau_conj_mem_range_rho
    · intro hh
      have := RankOne.FiveList.tau_conj_mem_range_rho hh
      rwa [tau_inv, ← mul_assoc, ← mul_assoc, tau_mul_tau, one_mul, mul_assoc, tau_mul_tau,
        mul_one] at this
  have hHN : H ≤ N := Subgroup.le_normalizer
  have : (H.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  set t : N ⧸ H.subgroupOf N := QuotientGroup.mk ⟨tau, htauN⟩
  have ht1 : t ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact RankOne.FiveList.tau_not_mem_range_rho h
  have ht2 : t ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨tau, htauN⟩ : N) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq, tau_mul_tau]
      rfl)
    rw [this, QuotientGroup.mk_one]
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have h2Q : 2 ∣ Nat.card (N ⧸ H.subgroupOf N) := by
    have h := orderOf_dvd_natCard t
    rwa [hto] at h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf N)
  have hsub : Nat.card (H.subgroupOf N) = 112896 := by
    rw [← hH]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hN : 2 * 112896 ∣ Nat.card N := by
    rw [hcard, hsub]
    exact Nat.mul_dvd_mul_right h2Q _
  exact ((by norm_num : 2 ^ 9 ∣ 2 * 112896).trans hN).trans (Subgroup.card_subgroup_dvd_card _)

end SevenList

open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem lFiveSevenL47SplitInput_holds : LFiveSevenL47SplitInput := by
  intro K _ _ hK A hsymm hS hA
  classical
  have hp : (7 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 7 ^ 1 := by rw [hK, pow_one]
  have : CharP K 7 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  set Z := center (SpecialLinearGroup (Fin 4) K)
  set ψ := CatalogueBHigherLinearAction.slConjugation 4 K A * slGraphAut 4 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 4 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 4) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 4 K A g
  have hfix : ∀ x : GL (Fin 4) K, A * glGraphAut 4 K x * A⁻¹ = x ↔
      glTranspose 4 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 4 K x = (glTranspose 4 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 4 K x * A⁻¹ * x =
          glTranspose 4 K x * A⁻¹ * (A * (glTranspose 4 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 4 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 4 K x)⁻¹ * (glTranspose 4 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  set IR := CatalogueBGraphForm.isometryGroup 4 K A⁻¹ with hIR
  set SLr := CatalogueBGeneralLinear.specialLinearRange 4 K with hSLr
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL = IR ⊓ SLr := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have hR := transpose_inv_of_transpose_eq A hsymm
  let Φ : IR ≃* TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
    (isometryGroupEquiv A⁻¹).symm.trans
      (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
  obtain ⟨S, hSd, hSQ⟩ := hS
  obtain ⟨-, e, -, -, -⟩ := CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
    (matrixQuadraticForm A⁻¹) (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
    (by rw [Module.finrank_fin_fun]) S hSd hSQ
  have h9 : 2 ^ 9 ∣ Nat.card IR := by
    rw [Nat.card_congr (Φ.trans e).toEquiv]
    exact SevenList.two_pow_nine_dvd_card_det hK
  let dI : IR →* Kˣ := Matrix.GeneralLinearGroup.det.comp IR.subtype
  have hsq1 : ∀ g : IR, dI g * dI g = 1 := fun g => by
    have hg : glTranspose 4 K (g : GL (Fin 4) K) * A⁻¹ * g = A⁻¹ := g.2
    have h1 := congrArg Matrix.GeneralLinearGroup.det hg
    rw [map_mul, map_mul] at h1
    have h2 : Matrix.GeneralLinearGroup.det (glTranspose 4 K (g : GL (Fin 4) K)) =
        Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) := by
      apply Units.ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, CatalogueBGraphForm.glTranspose_matrix,
        Matrix.det_transpose]
    rw [h2] at h1
    change Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) *
      Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) = 1
    have h3 : Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) *
        Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) * Matrix.GeneralLinearGroup.det A⁻¹ =
        1 * Matrix.GeneralLinearGroup.det A⁻¹ := by
      rw [one_mul, mul_right_comm, h1]
    exact mul_right_cancel h3
  have hpm1 : ∀ u ∈ dI.range, u = 1 ∨ u = -1 := by
    rintro u ⟨g, rfl⟩
    have h1 := congrArg Units.val (hsq1 g)
    rw [Units.val_mul, Units.val_one] at h1
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hm : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    have h2 : (2 : K) = 0 := by linear_combination -h'
    exact Ring.two_ne_zero hodd h2
  have hrange : Nat.card dI.range ≤ 2 := by
    have hle : dI.range ≤ Subgroup.zpowers (-1 : Kˣ) := by
      intro u hu
      rcases hpm1 u hu with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    have ho : orderOf (-1 : Kˣ) = 2 := orderOf_eq_prime (by rw [neg_one_sq]) hm
    calc Nat.card dI.range ≤ Nat.card (Subgroup.zpowers (-1 : Kˣ)) :=
          Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, ho]
  have hIRdvd : Nat.card IR ∣ 2 * Nat.card dI.ker := by
    rw [← Subgroup.card_ker_mul_card_range dI, mul_comm]
    exact Nat.mul_dvd_mul_right (RankOne.FiveList.card_dvd_two_of_le hrange) _
  have hker : Nat.card dI.ker = Nat.card (fixedSubgroup ψ) := by
    have h1 : (dI.ker).map IR.subtype = IR ⊓ SLr := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
        have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) = 1 := hg
        have hdv : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
          have := congrArg Units.val hdet
          simpa using this
        exact ⟨⟨(g : GL (Fin 4) K).val, hdv⟩, Units.ext rfl⟩
      · intro hy
        obtain ⟨hyI, ⟨x, rfl⟩⟩ := Subgroup.mem_inf.mp hy
        refine ⟨⟨_, hyI⟩, ?_, rfl⟩
        change Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL x) = 1
        apply Units.ext
        simp
    have e1 : Nat.card ((dI.ker).map IR.subtype) = Nat.card dI.ker :=
      Subgroup.card_map_of_injective IR.subtype_injective
    rw [← e1, h1, ← hmap, Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
  have hpmZ : ∀ z ∈ Z ⊓ fixedSubgroup ψ,
      (z : Matrix (Fin 4) (Fin 4) K) = 1 ∨ (z : Matrix (Fin 4) (Fin 4) K) = -1 := by
    intro z hz
    obtain ⟨hzZ, hzF⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzZ
    have hzI : SpecialLinearGroup.toGL z ∈ IR :=
      (Subgroup.mem_inf.mp (hmap ▸ ⟨z, hzF, rfl⟩ : SpecialLinearGroup.toGL z ∈ IR ⊓ SLr)).1
    have h1 : (glTranspose 4 K (SpecialLinearGroup.toGL z) * A⁻¹ *
        SpecialLinearGroup.toGL z).val = (A⁻¹ : GL (Fin 4) K).val := congrArg Units.val hzI
    rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix] at h1
    have hzv : (SpecialLinearGroup.toGL z).val = Matrix.scalar (Fin 4) r := hr.symm
    rw [hzv] at h1
    have h2 : (Matrix.scalar (Fin 4) r)ᵀ * (A⁻¹ : GL (Fin 4) K).val * Matrix.scalar (Fin 4) r =
        (r * r) • (A⁻¹ : GL (Fin 4) K).val := by
      rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    rw [h2] at h1
    have h3 : (r * r) • ((A⁻¹ : GL (Fin 4) K).val * (A : GL (Fin 4) K).val) =
        (A⁻¹ : GL (Fin 4) K).val * (A : GL (Fin 4) K).val := by
      rw [← smul_mul_assoc, h1]
    rw [Units.inv_mul] at h3
    have h4 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h3
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
    rcases mul_self_eq_one_iff.mp h4 with h5 | h5
    · left
      rw [← hr, h5, map_one]
    · right
      rw [← hr, h5, map_neg, map_one]
  have hneg : (-1 : Matrix (Fin 4) (Fin 4) K) ≠ 1 := by
    intro h
    have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h'
    have h2 : (2 : K) = 0 := by linear_combination -h'
    exact Ring.two_ne_zero hodd h2
  have hZf : Nat.card ↥(Z ⊓ fixedSubgroup ψ) ≤ 2 := by
    let fz : ↥(Z ⊓ fixedSubgroup ψ) → Bool :=
      fun z => decide (((z : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1)
    have hfz : Function.Injective fz := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      rcases hpmZ a a.2 with ha | ha <;> rcases hpmZ b b.2 with hb | hb
      · rw [ha, hb]
      · exfalso
        have h1 : fz a = true := by simp only [fz, ha, decide_true]
        have h2 : fz b = false := by simp only [fz, hb, hneg, decide_false]
        rw [h1, h2] at hab
        exact absurd hab (by decide)
      · exfalso
        have h1 : fz a = false := by simp only [fz, ha, hneg, decide_false]
        have h2 : fz b = true := by simp only [fz, hb, decide_true]
        rw [h1, h2] at hab
        exact absurd hab (by decide)
      · rw [ha, hb]
    calc Nat.card ↥(Z ⊓ fixedSubgroup ψ) ≤ Nat.card Bool := Nat.card_le_card_of_injective fz hfz
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hZ2 := RankOne.FiveList.card_dvd_two_of_le hZf
  have hfixd := RankOne.FiveList.card_fixed_dvd_card_inf_mul Z ψ hinv
  have hF : Nat.card (fixedSubgroup (pureGraphAction 4 K A)) =
      Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
    rw [heq]
  rw [hF]
  have h2F : Nat.card (fixedSubgroup ψ) ∣
      2 * Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) :=
    hfixd.trans (Nat.mul_dvd_mul_right hZ2 _)
  set F' := Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))
  have hA1 : 2 * Nat.card dI.ker ∣ 2 * (2 * F') := by
    rw [hker]
    exact Nat.mul_dvd_mul_left 2 h2F
  have h512 : 2 ^ 9 ∣ 4 * F' := by
    rw [show 4 * F' = 2 * (2 * F') by ring]
    exact h9.trans (hIRdvd.trans hA1)
  have h256 : 4 * 64 ∣ 4 * F' := (by norm_num : 4 * 64 ∣ 2 ^ 9).trans h512
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h256

section Holds


theorem lFiveSevenListFamilyInput_PSL_holds : LFiveSevenListFamilyInput .PSL :=
  lFiveSevenListFamilyInput_PSL_of_split lFiveSevenL47SplitInput_holds

theorem lFiveSevenRankFamilyInput_PSL_holds : LFiveSevenRankFamilyInput .PSL :=
  lFiveSevenRankFamilyInput_of_list lFiveSevenListFamilyInput_PSL_holds

end Holds

end CFSG.SeitzReduction.LinearPilot
