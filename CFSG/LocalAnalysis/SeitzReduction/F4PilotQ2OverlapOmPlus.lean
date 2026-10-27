module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlusData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOOmega

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.SeitzReduction.SymplecticPilot (kOmegaVec kOmegaEmb zThreeMat q2OmIota kOmegaBetaC
  kOmegaFixRes nsTorusSp nsElt mat_nsElt)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Two

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem omHirr (hK : Nat.card K = 2) : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro s
  rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK s with rfl | rfl
  · simp
  · rw [one_pow, one_mul, CharTwo.add_self_eq_zero, zero_add]
    exact one_ne_zero

theorem omXi_omMat : omMat K (omXi : Matrix (Fin 2) (Fin 2) (ZMod 2)) = omXi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omXi]

theorem zThreeMat_omMat : omMat K (zThreeMat : Matrix (Fin 2) (Fin 2) (ZMod 2)) = zThreeMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zThreeMat, CharTwo.neg_eq]

theorem blockMat_omMat {κ : Type} [DecidableEq κ] (p q : κ) (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    (blockMat p q A : Matrix κ κ (ZMod 2)).map (omCast K) = blockMat p q (omMat K A) := by
  ext a b
  simp only [blockMat, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem omMat_one_add_single {κ : Type} [Fintype κ] [DecidableEq κ] (a b : κ) :
    omMat K (1 + single a b (1 : ZMod 2)) = 1 + single a b 1 := by
  change (1 + single a b (1 : ZMod 2)).map (omCast K) = _
  rw [Matrix.map_add _ (map_add (omCast K)), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_single, map_one]

theorem omMat_zero' {ι κ : Type} : omMat K (0 : Matrix ι κ (ZMod 2)) = 0 :=
  Matrix.map_zero _ (map_zero (omCast K))

theorem omMat_fromBlocks_one {ι₆ : Type} [Fintype ι₆] [DecidableEq ι₆]
    (D : Matrix ι₆ ι₆ (ZMod 2)) :
    omMat K (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 D) =
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 (omMat K D) := by
  rw [omMat_fromBlocks, omMat_one, omMat_zero', omMat_zero']

theorem centralizer_zpowers_om {G : Type*} [Group G] (y : G) :
    centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem natCard_range_of_injective {A B : Type*} [Group A] [Group B] {φ : A →* B}
    (hφ : Function.Injective φ) : Nat.card φ.range = Nat.card A :=
  (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

end Two

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

include hK in
theorem omP_isom {A : Matrix omPI omPI (ZMod 2)}
    (hA : ∀ v, StatedQuadPlus (3 + 1) (ZMod 2) (A *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v) :
    ∀ w : omPI → K, StatedQuadPlus (3 + 1) K (omMat K A *ᵥ w) = StatedQuadPlus (3 + 1) K w :=
  omIsom hK (statedQuadPlus_omCast (3 + 1)) hA

include hK in
theorem omM6_isom {A : Matrix omMI6 omMI6 (ZMod 2)}
    (hA : ∀ v, StatedQuadMinus 3 (ZMod 2) 1 1 (A *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v) :
    ∀ w : omMI6 → K, StatedQuadMinus 3 K 1 1 (omMat K A *ᵥ w) = StatedQuadMinus 3 K 1 1 w :=
  omIsom hK (statedQuadMinus_omCast 3) hA

@[expose] def omPXhK : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  ⟨omGL K omPXh omPXhi omPXh_mul_inv, by
    rw [← omGL_commutator omPR1 omPR1 omPR2 omPR2 omPXh omPXhi omPR1_sq omPR2_sq
      omPXh_mul_inv omPXh_eq]
    exact commutator_mem_statedOmega (omP_isom hK omPR1_isom) (omP_isom hK omPR2_isom)⟩

@[expose] def omPULK : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  ⟨omGL K omPUL omPUL omPUL_sq, by
    rw [← omGL_commutator omPLev13 omPLev13 omPRv omPRv omPUL omPUL omPLev13_sq omPRv_sq
      omPUL_sq omPUL_eq]
    exact commutator_mem_statedOmega (omP_isom hK omPLev13_isom) (omP_isom hK omPRv_isom)⟩

@[expose] def omPUSK : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  ⟨omGL K omPUS omPUS omPUS_sq, by
    rw [← omGL_commutator omPLev10 omPLev10 omPSie02 omPSie02 omPUS omPUS omPLev10_sq
      omPSie02_sq omPUS_sq omPUS_eq]
    exact commutator_mem_statedOmega (omP_isom hK omPLev10_isom) (omP_isom hK omPSie02_isom)⟩

@[expose] def omPHLK : StatedOmega (StatedQuadMinus 3 K 1 1) :=
  ⟨omGL K omPHL omPHL omPHL_sq, by
    rw [← omGL_commutator omPE3 omPE3 omPE4 omPE4 omPHL omPHL omPE3_sq omPE4_sq omPHL_sq
      omPHL_eq]
    exact commutator_mem_statedOmega (omM6_isom hK omPE3_isom) (omM6_isom hK omPE4_isom)⟩

@[expose] def omPHSK : StatedOmega (StatedQuadMinus 3 K 1 1) :=
  ⟨omGL K omPHS omPHS omPHS_sq, by
    rw [← omGL_commutator omPE1 omPE1 omPE2 omPE2 omPHS omPHS omPE1_sq omPE2_sq omPHS_sq
      omPHS_eq]
    exact commutator_mem_statedOmega (omM6_isom hK omPE1_isom) (omM6_isom hK omPE2_isom)⟩

theorem omPT_mul_TiK : omMat K omPT * omMat K omPTi = 1 := by
  rw [← omMat_mul, omPT_mul_Ti, omMat_one]

theorem omPTi_mul_TK : omMat K omPTi * omMat K omPT = 1 := by
  rw [← omMat_mul, omPTi_mul_T, omMat_one]

include hK in
theorem omPT_quadK : ∀ w : omPI' → K, StatedQuadPlus (3 + 1) K (omMat K omPT *ᵥ w) =
    omQP (w ∘ Sum.inl) + StatedQuadMinus 3 K 1 1 (w ∘ Sum.inr) := by
  intro w
  obtain ⟨v, rfl⟩ := exists_omCast_comp hK w
  rw [omMat_mulVec, statedQuadPlus_omCast, omPT_quad, map_add, Function.comp_assoc,
    Function.comp_assoc, statedQuadMinus_omCast]
  congr 1
  simp [omQP]

theorem omPTi_xh_TK : omMat K omPTi * ((omPXhK hK : GL omPI K) : Matrix omPI omPI K) *
    omMat K omPT = fromBlocks omXi 0 0 1 := by
  change omMat K omPTi * omMat K omPXh * omMat K omPT = _
  rw [← omMat_mul, ← omMat_mul, omPTi_xh_T, omMat_fromBlocks, omXi_omMat, omMat_one, omMat_zero',
    omMat_zero']

theorem perfectCore_centralizer_omPXhK :
    perfectCore (centralizer ({omPXhK hK} : Set (StatedOmega (StatedQuadPlus (3 + 1) K)))) =
      (omEps0 (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP) (Q₆ := StatedQuadMinus 3 K 1 1)
        omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK)).range :=
  perfectCore_centralizer_omOrth omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK) (omPTi_xh_TK hK)
    (commutator_statedOmega_quadMinus_three (omHirr hK))

theorem omEps0_omPHLK :
    omEps0 (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP) (Q₆ := StatedQuadMinus 3 K 1 1)
      omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK) (omPHLK hK) = omPULK hK := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omEps0, coe_omEps]
  change omMat K omPT * fromBlocks 1 0 0 (omMat K omPHL) * omMat K omPTi = omMat K omPUL
  rw [← omMat_fromBlocks_one, ← omMat_mul, ← omMat_mul, omPT_hL_Ti]

theorem omEps0_omPHSK :
    omEps0 (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP) (Q₆ := StatedQuadMinus 3 K 1 1)
      omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK) (omPHSK hK) = omPUSK hK := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omEps0, coe_omEps]
  change omMat K omPT * fromBlocks 1 0 0 (omMat K omPHS) * omMat K omPTi = omMat K omPUS
  rw [← omMat_fromBlocks_one, ← omMat_mul, ← omMat_mul, omPT_hS_Ti]

end Plus

section Lifts

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

theorem kOmegaVec_omCast : kOmegaVec K 3 = omCast K ∘ kOmegaVec (ZMod 2) 3 := by
  funext a
  simp only [Function.comp_apply, SymplecticPilot.kOmegaVec, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

include hK in
theorem q2OmIota_eq_of_res (g : StatedSp 3 K) (A : StatedOmega (StatedQuadPlus (3 + 1) K))
    (hfix : ((A : GL omPI K) : Matrix omPI omPI K) *ᵥ kOmegaVec K 3 = kOmegaVec K 3)
    (hres : ((A : GL omPI K) : Matrix omPI omPI K).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
      mat 3 K g) :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl g = A := by
  have hA : A ∈ fixedSubgroup (kOmegaBetaC K 3) :=
    (SymplecticPilot.mem_fixedSubgroup_kOmegaBetaC_iff K (by norm_num) A).2 hfix
  obtain ⟨y, hy, hyg⟩ :=
    SymplecticPilot.kOmegaFixRes_q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl g
  have hyA : y = ⟨A, hA⟩ := by
    apply SymplecticPilot.kOmegaFixRes_injective_two K (by norm_num) hK le_rfl
    rw [hyg]
    apply mat_injective
    rw [mat_apply (x := SymplecticPilot.kOmegaFixRes K _ _), SymplecticPilot.coe_kOmegaFixRes]
    exact hres.symm
  rw [← hy, hyA]

theorem q2OmIota_nsElt :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (nsElt 0) = omPXhK hK := by
  refine q2OmIota_eq_of_res hK _ _ ?_ ?_
  · change omMat K omPXh *ᵥ kOmegaVec K 3 = kOmegaVec K 3
    rw [kOmegaVec_omCast, omMat_mulVec, omPXh_mulVec_vec]
  · change (omPXh.submatrix (kOmegaEmb 3) (kOmegaEmb 3)).map (omCast K) = mat 3 K (nsElt 0)
    rw [mat_nsElt, omPXh_submatrix, blockMat_omMat, zThreeMat_omMat]

theorem q2OmIota_eltL :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl (elt (.positiveLong 1) 1) =
      omPULK hK := by
  refine q2OmIota_eq_of_res hK _ _ ?_ ?_
  · change omMat K omPUL *ᵥ kOmegaVec K 3 = kOmegaVec K 3
    rw [kOmegaVec_omCast, omMat_mulVec, omPUL_mulVec_vec]
  · change (omPUL.submatrix (kOmegaEmb 3) (kOmegaEmb 3)).map (omCast K) = _
    rw [omPUL_submatrix, mat_elt_positiveLong]
    exact omMat_one_add_single _ _

theorem q2OmIota_eltS :
    q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl
      (elt (.positiveSum 1 2 (by decide)) 1) = omPUSK hK := by
  refine q2OmIota_eq_of_res hK _ _ ?_ ?_
  · change omMat K omPUS *ᵥ kOmegaVec K 3 = kOmegaVec K 3
    rw [kOmegaVec_omCast, omMat_mulVec, omPUS_mulVec_vec]
  · change (omPUS.submatrix (kOmegaEmb 3) (kOmegaEmb 3)).map (omCast K) = _
    rw [omPUS_submatrix, mat_elt, one_smul]
    change (1 + (single _ _ (1 : ZMod 2) + single _ _ 1)).map (omCast K) = _
    rw [Matrix.map_add _ (map_add (omCast K)), Matrix.map_add _ (map_add (omCast K)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, Matrix.map_single, map_one]
    rfl

end Lifts

@[expose] def OmSixMinusCentValues : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
    Nat.card (centralizer ({omPHLK hK} : Set (StatedOmega (StatedQuadMinus 3 K 1 1)))) = 96 ∧
      Nat.card (centralizer ({omPHSK hK} : Set (StatedOmega (StatedQuadMinus 3 K 1 1)))) = 576

theorem twoOmegaPlusModelValues_of_six (h6 : OmSixMinusCentValues) :
    TwoOmegaPlusModelValues := by
  intro K _ _ _ hK
  have hcore : centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl)) =
      (omEps0 (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP) (Q₆ := StatedQuadMinus 3 K 1 1)
        omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK)).range := by
    rw [centralizerPerfectCore_def, SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers,
      centralizer_zpowers_om, q2OmIota_nsElt hK, perfectCore_centralizer_omPXhK hK]
  have hinj := omEps0_injective (Q₈ := StatedQuadPlus (3 + 1) K) (QP := omQP)
    (Q₆ := StatedQuadMinus 3 K 1 1) omPT_mul_TiK omPTi_mul_TK (omPT_quadK hK)
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [hcore, natCard_range_of_injective hinj, natCard_statedOmega_quadMinus_three (omHirr hK),
      hK]
    decide
  · rw [centralizer_map_rootGroup_eq hK _ stdVec_positiveLong_one, hcore, q2OmIota_eltL hK,
      ← omEps0_omPHLK hK, card_centralizer_singleton_inf_range hinj, (h6 K hK).1]
    rfl
  · rw [centralizer_map_rootGroup_eq hK _ stdVec_positiveSum_one_two, hcore, q2OmIota_eltS hK,
      ← omEps0_omPHSK hK, card_centralizer_singleton_inf_range hinj, (h6 K hK).2]
    rfl

end CFSG.SeitzReduction.F4Pilot
