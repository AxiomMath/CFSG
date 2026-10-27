module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenU47
import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Field
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpBasic
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSL

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem mem_range_conj_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α : MulAut X}
    (h : MulAut.congr e α ∈ (MulAut.conj : Y →* MulAut Y).range) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 := congrArg (fun β : MulAut Y => β (e x)) hy
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h1

theorem sixteen_dvd_card_fixed_psl_two_fortyNine
    {S : Type} [Group S] [Finite S] (hS : LieModel S .PSL 2 7 2)
    {τ : MulAut S} (hτ : orderOf τ = 2) (hout : τ ∉ (MulAut.conj : S →* MulAut S).range)
    (h8 : 2 ^ 3 ∣ Nat.card (fixedSubgroup τ)) : 2 ^ 4 ∣ Nat.card (fixedSubgroup τ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hS
  have hodd := AutL2Facts.isOddPrimePower_of hp (by norm_num) hf hF
  have hττ : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  by_cases hlin : τ ∈ FooteLit.Aut5L2.linL2 e
  ·
    exfalso
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
    set P' : Subgroup S := P.map (fixedSubgroup τ).subtype with hP'
    have hP'c : Nat.card P' = 2 ^ 3 := by
      rw [hP', card_map_of_injective (fixedSubgroup τ).subtype_injective, hP]
    obtain ⟨R, hR⟩ := (IsPGroup.of_card hP'c).exists_le_sylow
    have hle : P' ≤ (R : Subgroup S) ⊓ MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) := by
      intro x hx
      refine ⟨hR hx, ?_⟩
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have h1 := card_le_of_le hle
    rw [hP'c, show (2 : ℕ) ^ 3 = 8 by norm_num] at h1
    have h2 := FooteLit.Aut5L2.pgl_fixed_l2 e hodd R τ hlin hout hττ
    omega
  ·
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 S))
    obtain ⟨g, hg⟩ := FooteLit.Aut5L2.conj_centralizer_l2 e hp (by norm_num) hf hF R τ hlin hττ
    have hS16 : 2 ^ 4 ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F hodd, hF]
      norm_num
    have hR16 := R.pow_dvd_card_of_pow_dvd_card hS16
    set Q : Subgroup S := (R : Subgroup S).map (MulAut.conj g⁻¹).toMonoidHom with hQ
    have hQc : Nat.card Q = Nat.card (R : Subgroup S) :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    have hQle : Q ≤ fixedSubgroup τ := by
      rintro _ ⟨r, hr, rfl⟩
      have h1 := hg r hr
      simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply] at h1
      change τ (MulAut.conj g⁻¹ r) = MulAut.conj g⁻¹ r
      rw [MulAut.conj_apply, inv_inv]
      calc τ (g⁻¹ * r * g) = g⁻¹ * (g * τ (g⁻¹ * r * g) * g⁻¹) * g := by group
        _ = g⁻¹ * r * g := by rw [h1]
    exact (hQc ▸ hR16).trans (card_dvd_of_le hQle)

open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem dvd_card_fixed_pureGraph_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7)
    (A : GL (Fin 3) K) (hA : orderOf (pureGraphAction 3 K A) = 2) :
    336 ∣ Nat.card (fixedSubgroup (pureGraphAction 3 K A)) := by
  classical
  have hp : (7 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 7 ^ 1 := by rw [hK, pow_one]
  have : CharP K 7 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 7]
    norm_num
  have hsq2 : pureGraphAction 3 K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hsymm : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A := by
    rcases CatalogueBGraphForm.pureGraph_involution_form_data 3 K le_rfl hodd A hsq2 with h | h
    · exact h
    · exact absurd h.2 (by decide)
  set Z := center (SpecialLinearGroup (Fin 3) K)
  set ψ := CatalogueBHigherLinearAction.slConjugation 3 K A * slGraphAut 3 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 3 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 3) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 3 K A g
  have hfix : ∀ x : GL (Fin 3) K, A * glGraphAut 3 K x * A⁻¹ = x ↔
      glTranspose 3 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 3 K x = (glTranspose 3 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 3 K x * A⁻¹ * x =
          glTranspose 3 K x * A⁻¹ * (A * (glTranspose 3 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 3 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 3 K x)⁻¹ * (glTranspose 3 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  set IR := CatalogueBGraphForm.isometryGroup 3 K A⁻¹ with hIR
  set SLr := CatalogueBGeneralLinear.specialLinearRange 3 K with hSLr
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
  have h672 : Nat.card IR = 672 := by
    have hO := GroupTheory.WeirSylow.natCard_orthogonalGroup_odd hodd
      (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR) (n := 1)
      (by rw [Module.finrank_fin_fun])
    rw [hK] at hO
    have hO' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) : ℤ)
        = 672 := by
      rw [hO]
      simp [Finset.Icc_self]
    rw [Nat.card_congr Φ.toEquiv]
    exact_mod_cast hO'
  let dI : IR →* Kˣ := Matrix.GeneralLinearGroup.det.comp IR.subtype
  have hsq1 : ∀ g : IR, dI g * dI g = 1 := fun g => by
    have hg : glTranspose 3 K (g : GL (Fin 3) K) * A⁻¹ * g = A⁻¹ := g.2
    have h1 := congrArg Matrix.GeneralLinearGroup.det hg
    rw [map_mul, map_mul] at h1
    have h2 : Matrix.GeneralLinearGroup.det (glTranspose 3 K (g : GL (Fin 3) K)) =
        Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) := by
      apply Units.ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, CatalogueBGraphForm.glTranspose_matrix,
        Matrix.det_transpose]
    rw [h2] at h1
    change Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) *
      Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) = 1
    have h3 : Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) *
        Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) * Matrix.GeneralLinearGroup.det A⁻¹ =
        1 * Matrix.GeneralLinearGroup.det A⁻¹ := by
      rw [one_mul, mul_right_comm, h1]
    exact mul_right_cancel h3
  have hrange : Nat.card dI.range ≤ 2 := by
    have hle : dI.range ≤ Subgroup.zpowers (-1 : Kˣ) := by
      rintro u ⟨g, rfl⟩
      have h1 := congrArg Units.val (hsq1 g)
      rw [Units.val_mul, Units.val_one] at h1
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · rw [show dI g = 1 from Units.ext h]
        exact one_mem _
      · rw [show dI g = -1 from Units.ext (by rw [h, Units.val_neg, Units.val_one])]
        exact Subgroup.mem_zpowers _
    calc Nat.card dI.range ≤ Nat.card (Subgroup.zpowers (-1 : Kˣ)) := Subgroup.card_le_of_le hle
      _ = orderOf (-1 : Kˣ) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [neg_one_sq])
  have hIRdvd : Nat.card IR ∣ 2 * Nat.card dI.ker := by
    rw [← Subgroup.card_ker_mul_card_range dI, mul_comm]
    exact Nat.mul_dvd_mul_right (SeitzReduction.RankOne.FiveList.card_dvd_two_of_le hrange) _
  have hker : Nat.card dI.ker = Nat.card (fixedSubgroup ψ) := by
    have h1 : (dI.ker).map IR.subtype = IR ⊓ SLr := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
        have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) = 1 := hg
        have hdv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
          have := congrArg Units.val hdet
          simpa using this
        exact ⟨⟨(g : GL (Fin 3) K).val, hdv⟩, Units.ext rfl⟩
      · intro hy
        obtain ⟨hyI, ⟨x, rfl⟩⟩ := Subgroup.mem_inf.mp hy
        refine ⟨⟨_, hyI⟩, ?_, rfl⟩
        change Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL x) = 1
        apply Units.ext
        simp
    have e1 : Nat.card ((dI.ker).map IR.subtype) = Nat.card dI.ker :=
      Subgroup.card_map_of_injective IR.subtype_injective
    rw [← e1, h1, ← hmap, Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
  have hZf : Z ⊓ fixedSubgroup ψ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzZ, hzF⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzZ
    rw [Fintype.card_fin] at hr3
    have hzI : SpecialLinearGroup.toGL z ∈ IR :=
      (Subgroup.mem_inf.mp (hmap ▸ ⟨z, hzF, rfl⟩ : SpecialLinearGroup.toGL z ∈ IR ⊓ SLr)).1
    have h1 : (glTranspose 3 K (SpecialLinearGroup.toGL z) * A⁻¹ *
        SpecialLinearGroup.toGL z).val = (A⁻¹ : GL (Fin 3) K).val := congrArg Units.val hzI
    rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix] at h1
    have hzv : (SpecialLinearGroup.toGL z).val = Matrix.scalar (Fin 3) r := hr.symm
    rw [hzv] at h1
    have h2 : (Matrix.scalar (Fin 3) r)ᵀ * (A⁻¹ : GL (Fin 3) K).val * Matrix.scalar (Fin 3) r =
        (r * r) • (A⁻¹ : GL (Fin 3) K).val := by
      rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    rw [h2] at h1
    have h3 : (r * r) • ((A⁻¹ : GL (Fin 3) K).val * (A : GL (Fin 3) K).val) =
        (A⁻¹ : GL (Fin 3) K).val * (A : GL (Fin 3) K).val := by
      rw [← smul_mul_assoc, h1]
    rw [Units.inv_mul] at h3
    have h4 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h3
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
    have hr1 : r = 1 := by
      have h5 : r ^ 3 = r * r * r := by ring
      rw [h5, h4, one_mul] at hr3
      exact hr3
    rw [Subgroup.mem_bot]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hfixd := SeitzReduction.RankOne.FiveList.card_fixed_dvd_card_inf_mul Z ψ hinv
  rw [hZf, card_bot, one_mul] at hfixd
  have hF : Nat.card (fixedSubgroup (pureGraphAction 3 K A)) =
      Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
    rw [heq]
  rw [hF]
  have h1 : 672 ∣ 2 * Nat.card (fixedSubgroup ψ) := by
    rw [← hker, ← h672]
    exact hIRdvd
  have h2 : 336 ∣ Nat.card (fixedSubgroup ψ) := by omega
  exact h2.trans hfixd

theorem dvd_card_fixed_psl_three_seven {S : Type} [Group S] [Finite S]
    (hSm : LieModel S .PSL 3 7 1) {τ : MulAut S} (hτ : orderOf τ = 2)
    (hout : τ ∉ (MulAut.conj : S →* MulAut S).range) : 336 ∣ Nat.card (fixedSubgroup τ) := by
  have hadm : StatedLieAdmissible .PSL 3 7 1 :=
    SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hSm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hSm
  have hK7 : Nat.card K = 7 := by rw [hK, pow_one]
  have hτ2 : τ ^ 2 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hβ : orderOf (MulAut.congr e τ) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ
  have hcard : Nat.card (fixedSubgroup τ) = Nat.card (fixedSubgroup (MulAut.congr e τ)) :=
    Nat.card_congr (CatLeafProof.fixedSubgroupCongrEquiv e τ).toEquiv
  obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := K) (le_refl 3)
  obtain ⟨A, σ, ε, hε, hAσε⟩ :=
    hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv 3 K).symm (MulAut.congr e τ))
  obtain rfl := SeitzReduction.LinearPilot.SevenList.ringEquiv_eq_one hK7 σ
  interval_cases ε
  ·
    exfalso
    apply hout
    rw [map_one, mul_one, pow_zero, mul_one] at hAσε
    have hA2 : LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K (A ^ 2) = 1 := by
      rw [map_pow, ← hAσε, ← map_pow, ← map_pow, hτ2, map_one, map_one]
    obtain ⟨c, hc⟩ := (RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl (A ^ 2)).mp hA2
    have hdet : Matrix.GeneralLinearGroup.det A =
        (Matrix.GeneralLinearGroup.det A * c⁻¹) ^ 3 := by
      have h3 := congrArg Matrix.GeneralLinearGroup.det hc
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow] at h3
      rw [mul_pow, inv_pow, h3]
      group
    have hin :=
      RankThree.PartTwo.KFacts.OutFixCentralThree.conjAut_mem_range_conj_of_det hdet
    rw [← hAσε] at hin
    exact mem_range_conj_of_congr e (mem_range_conj_of_congr _ hin)
  ·
    rw [map_one, mul_one, pow_one] at hAσε
    have hβ' : MulAut.congr e τ = CatalogueBGraphForm.pureGraphAction 3 K A := by
      rw [← CatalogueBLinearHigherB.congr_pureGraph, ← hAσε]
      ext x
      simp
    rw [hcard, hβ']
    exact dvd_card_fixed_pureGraph_three hK7 A (hβ' ▸ hβ)

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem dvd_card_fixed_psu_three_graph {K : Type} [Field K] (h : UnitaryFieldData 7 1 K)
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    336 ∣ Nat.card (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) := by
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd 7 := by decide
  have : Fact (7 : ℕ).Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC (by norm_num) _).mp hx2
  have hmapA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar := Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin 3) K) * glAut φ (A : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set Z := normOneScalars h (gramSU h (idGram K 3)) 3 with hZdef
  set ψ : MulAut (gramSU h (idGram K 3)) :=
    primeFormConjSU h (idGram K 3) A * primeFormFieldSU h hC φ with hψdef
  have hinv : Z.map ψ.toMonoidHom = Z := by
    have e1 : ψ.toMonoidHom = (primeFormConjSU h (idGram K 3) A).toMonoidHom.comp
        (primeFormFieldSU h hC φ).toMonoidHom := rfl
    rw [e1, ← Subgroup.map_map, map_normOneScalars_field, map_normOneScalars_conj]
  have heq : primeFormPsi h hC ⟨A, φ⟩ = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : primeFormP h (idGram K 3))) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk, primeFormPsi_apply, MulAut.mul_apply]
      change primeFormConjAut h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
      rw [primeFormFieldAut_mk, primeFormConjAut_mk]
      rfl
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ :=
    CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  let φS : gramSU h (idGram K 3) →* LinearMap.GeneralLinearGroup K (Fin 3 → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) K ≃*
      LinearMap.GeneralLinearGroup K (Fin 3 → K)).toMonoidHom.comp
        (gramSU h (idGram K 3)).subtype
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hxy)
  have hfixg : ∀ g : gramSU h (idGram K 3), g ∈ fixedSubgroup ψ ↔
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar := by
    intro g
    change ψ g = g ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin 3) K) * glAut φ (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ = g ↔ _
    rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut]
    have hmap : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar := Matrix.ext fun i j => hφ _
    rw [hmap]
    exact eq_comm
  have htoLin : ∀ (g : GL (Fin 3) K) (v : Fin 3 → K),
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := fun g v => by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hmap : (fixedSubgroup ψ).map φS =
      commutingUnitary (idForm h 3) τ₀ ⊓ sesqSpecialUnitaryGroup (idForm h 3) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hS : φS g ∈ sesqSpecialUnitaryGroup (idForm h 3) :=
        (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K 3) g).mpr g.2
      refine Subgroup.mem_inf.mpr ⟨⟨sesqSpecialUnitaryGroup_le _ hS, fun v => ?_⟩, hS⟩
      change ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
            (τ₀ v) = τ₀ (((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) :
              LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v)
      rw [htoLin, htoLin]
      exact (CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mpr ((hfixg g).mp hg) v
    · intro hy
      obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
      set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K 3) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hyS
      refine ⟨⟨g, hg⟩, (hfixg _).mpr
        ((CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mp
        fun v => ?_), hgy⟩
      have h1 := hyC.2 v
      rw [← hgy, htoLin, htoLin] at h1
      exact h1
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; omega) (idForm_isSymm h 3) (idForm_separatingLeft h 3)
    τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 7 ^ 1 := h.card_fixedField
  have hdimW : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 2 * 1 + 1 := by
    rw [hfinW, Module.finrank_fin_fun]
  have h672 : Nat.card (commutingUnitary (idForm h 3) τ₀) = 672 := by
    rcases hμ1 with hμ1 | hμ1
    ·
      obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
      have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
        have h1 := congrArg h.fixedField.subtype h0
        rw [map_ofNat, map_zero] at h1
        exact two_ne_zero_of_odd h hp2 h1
      have hchar : ringChar h.fixedField ≠ 2 := by
        intro h0
        apply h2
        have h1 := ringChar.Nat.cast_ringChar (R := h.fixedField)
        rw [h0] at h1
        exact_mod_cast h1
      have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
        rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
        exact hnd
      let Ψ := Φ.trans (MulEquiv.subgroupCongr
        (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
      have hO := GroupTheory.WeirSylow.natCard_orthogonalGroup_odd hchar hQ (n := 1) hdimW
      rw [hkc] at hO
      have hO' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')) : ℤ) = 672 := by
        rw [hO]
        simp [Finset.Icc_self]
      rw [Nat.card_congr Ψ.toEquiv]
      exact_mod_cast hO'
    ·
      obtain ⟨-, -, -, -, hev, -, -⟩ := hB2 hμ1
      rw [Module.finrank_fin_fun] at hev
      exact absurd hev (by decide)
  have hCS : Nat.card (commutingUnitary (idForm h 3) τ₀) = Nat.card (fixedSubgroup ψ) *
      (sesqSpecialUnitaryGroup (idForm h 3)).relIndex (commutingUnitary (idForm h 3) τ₀) := by
    have h1 := Subgroup.card_mul_index ((sesqSpecialUnitaryGroup (idForm h 3)).subgroupOf
      (commutingUnitary (idForm h 3) τ₀))
    have h2 : Nat.card ((sesqSpecialUnitaryGroup (idForm h 3)).subgroupOf
        (commutingUnitary (idForm h 3) τ₀)) = Nat.card (fixedSubgroup ψ) := by
      rw [← Subgroup.inf_subgroupOf_right (sesqSpecialUnitaryGroup (idForm h 3))
          (commutingUnitary (idForm h 3) τ₀),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, ← hmap,
        Subgroup.card_map_of_injective hφS]
    rw [← h1, h2]
    rfl
  have hidx : (sesqSpecialUnitaryGroup (idForm h 3)).relIndex
      (commutingUnitary (idForm h 3) τ₀) ∣ 2 :=
    SeitzReduction.LinearPilot.SevenList.relIndex_commutingUnitary_dvd_two h (A : GL (Fin 3) K)
  have h336 : 336 ∣ Nat.card (fixedSubgroup ψ) := by
    rw [h672] at hCS
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h1 <;> rw [h1] at hCS <;> omega
  have hZ : Nat.card Z = 1 := by
    rw [hZdef, RankThree.Classical.card_normOneScalars_one h (by norm_num)]
    norm_num
  have hfixd := SeitzReduction.RankOne.FiveList.card_fixed_dvd_card_mul Z ψ hinv
  rw [hZ, one_mul] at hfixd
  rw [heq]
  exact h336.trans hfixd

theorem dvd_card_fixed_psu_three_seven
    {S : Type} [Group S] [Finite S]
    (hm : LieModel S .PSU 3 7 1) {τ : MulAut S} (hτ : orderOf τ = 2)
    (hF : SeitzReduction.LinearPilot.SevenL3Group (fixedSubgroup τ)) :
    336 ∣ Nat.card (fixedSubgroup τ) := by
  have hadm : StatedLieAdmissible .PSU 3 7 1 :=
    SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hm
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hq : ¬(3 = 3 ∧ 7 ^ 1 = 2) := by norm_num
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ τ) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective τ).trans hτ
  have hFβ := hF.congr ψ
  have hcard : Nat.card (fixedSubgroup τ) = Nat.card (fixedSubgroup (MulAut.congr ψ τ)) :=
    Nat.card_congr (CatLeafProof.fixedSubgroupCongrEquiv ψ τ).toEquiv
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC le_rfl hq (MulAut.congr ψ τ)
  have hff : primeFormFieldFactor h hC le_rfl hq (MulAut.congr ψ τ) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ τ)
    rw [hβ] at h1
    rw [h1, map_one]
  rcases UnitaryHigher.ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · exfalso
    have hAα : MulAut.congr ψ τ = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    exact SeitzReduction.LinearPilot.lFiveSevenPSUInnerInput_holds 3 K 1 h hadm A (hAα ▸ hβ)
      (hFβ.of_eq hAα)
  · rw [hcard, ← hAφ]
    exact dvd_card_fixed_psu_three_graph h A φ hφ (hAφ ▸ hβ)

end Unitary

end CFSG.LocalAnalysis.EvenBN.TrialityD4
