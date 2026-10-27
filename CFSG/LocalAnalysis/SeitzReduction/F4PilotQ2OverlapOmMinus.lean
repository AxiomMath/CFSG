module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinusData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmChain
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.SeitzReduction.SymplecticPilot (kOmMVec kOmMEmb zThreeMat q2OmMIota kOmMBetaC
  kOmMFixRes nsTorusSp nsElt mat_nsElt)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap
  closure_isometries_eq_comap)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Klein

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.RankThree.PartOne.K159 in
theorem omKlein_facts :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)⁆ =
      (Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _).range ∧
      Group.IsPerfect (Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _).range ∧
      Nat.card (Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _).range =
        Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) ∧
      ((Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _).range.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))).index = 2 := by
  obtain ⟨hs, hp⟩ := Klein.sl4_isSimpleGroup_and_perfect (K := K)
  have hle : (Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _).range ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
    rintro _ ⟨g, rfl⟩
    exact Klein.rho_mem g
  obtain ⟨-, hperf, -, hcard, hidx, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.derived_of_index_two_model
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) Klein.rho Klein.rho_injective hle
      Klein.card_orthogonalGroup_quadPlus_three
  exact ⟨hcomm, hperf, hcard, hidx⟩

theorem statedOmega_quadPlus_three_eq_map :
    StatedOmega (StatedQuadPlus 3 K) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)⁆.map
        (toLinEquiv (Fin 3 ⊕ Fin 3) K).symm.toMonoidHom := by
  rw [statedOmega_eq_comap (coe_quadPlus 3 K), Subgroup.comap_equiv_eq_map_symm']

theorem commutator_statedOmega_quadPlus_three_any :
    ⁅StatedOmega (StatedQuadPlus 3 K), StatedOmega (StatedQuadPlus 3 K)⁆ =
      StatedOmega (StatedQuadPlus 3 K) := by
  obtain ⟨hcomm, hperf, -, -⟩ := omKlein_facts (K := K)
  rw [← hcomm] at hperf
  rw [statedOmega_quadPlus_three_eq_map, ← Subgroup.map_commutator,
    Subgroup.isPerfect_iff.1 hperf]

theorem natCard_statedOmega_quadPlus_three_any :
    Nat.card (StatedOmega (StatedQuadPlus 3 K)) = ordSL 4 (Nat.card K) := by
  obtain ⟨hcomm, -, hcard, -⟩ := omKlein_facts (K := K)
  rw [statedOmega_quadPlus_three_eq_map, Subgroup.card_map_of_injective (MulEquiv.injective _),
    hcomm, hcard]
  exact natCard_specialLinearGroup_eq_ordSL (by norm_num)

theorem omIndex_quadPlus_three :
    ((StatedOmega (StatedQuadPlus 3 K)).subgroupOf
      (omIsoGroup (StatedQuadPlus 3 K))).index = 2 := by
  obtain ⟨hcomm, -, -, hidx⟩ := omKlein_facts (K := K)
  rw [← hcomm] at hidx
  have h1 := statedOmega_eq_comap (coe_quadPlus 3 K)
  have h2 : omIsoGroup (StatedQuadPlus 3 K) = (TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus 3 K)).comap (toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom := by
    rw [← closure_omIsoSet]
    exact closure_isometries_eq_comap (coe_quadPlus 3 K)
  change (StatedOmega (StatedQuadPlus 3 K)).relIndex (omIsoGroup (StatedQuadPlus 3 K)) = 2
  rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (toLinEquiv (Fin 3 ⊕ Fin 3) K).surjective]
  exact hidx

theorem omNotMem_quadPlus_three (g : GL (Fin 3 ⊕ Fin 3) K) (a : Fin 3 ⊕ Fin 3 → K)
    (ha : StatedQuadPlus 3 K a ≠ 0)
    (hg : ∀ v, (g : Matrix _ _ K) *ᵥ v = v - ((StatedQuadPlus 3 K a)⁻¹ *
      (StatedQuadPlus 3 K (a + v) - StatedQuadPlus 3 K a - StatedQuadPlus 3 K v)) • a) :
    g ∉ StatedOmega (StatedQuadPlus 3 K) := by
  intro hr
  obtain ⟨hQ, -⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := 3) le_rfl
  rw [statedOmega_eq_comap (coe_quadPlus 3 K), Subgroup.mem_comap] at hr
  have hmem := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hr
  have : Invertible (quadPlus 3 K a) := invertibleOfNonzero (by rw [coe_quadPlus]; exact ha)
  have heq : (toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom g =
      TauCeti.QuadraticMap.reflection (quadPlus 3 K) a := by
    apply LinearEquiv.ext
    intro v
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, TauCeti.QuadraticMap.reflection_apply,
      invOf_eq_inv, QuadraticMap.polar, coe_quadPlus]
    exact hg v
  rw [heq] at hmem
  have h1 := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.1 hmem).2
  rw [CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ] at h1
  exact Nat.not_even_one h1

end Klein

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

include hK in
theorem omN_isom {A : Matrix omNI omNI (ZMod 2)}
    (hA : ∀ v, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (A *ᵥ v) =
      StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v) :
    ∀ w : omNI → K, StatedQuadMinus (3 + 1) K 1 1 (omMat K A *ᵥ w) =
      StatedQuadMinus (3 + 1) K 1 1 w :=
  omIsom hK (statedQuadMinus_omCast (3 + 1)) hA

include hK in
theorem omP6_isom {A : Matrix omPI6 omPI6 (ZMod 2)}
    (hA : ∀ v, StatedQuadPlus 3 (ZMod 2) (A *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v) :
    ∀ w : omPI6 → K, StatedQuadPlus 3 K (omMat K A *ᵥ w) = StatedQuadPlus 3 K w :=
  omIsom hK (statedQuadPlus_omCast 3) hA

@[expose] def omNXhK : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) :=
  ⟨omGL K omNXh omNXhi omNXh_mul_inv, by
    rw [← omGL_commutator omNX1 omNX1 omNX2 omNX2 omNXh omNXhi omNX1_sq omNX2_sq
      omNXh_mul_inv omNXh_eq]
    exact commutator_mem_statedOmega (omN_isom hK omNX1_isom) (omN_isom hK omNX2_isom)⟩

@[expose] def omNULK : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) :=
  ⟨omGL K omNUL omNUL omNUL_sq, by
    rw [← omGL_commutator omNL1 omNL1 omNL2 omNL2 omNUL omNUL omNL1_sq omNL2_sq omNUL_sq
      omNUL_eq]
    exact commutator_mem_statedOmega (omN_isom hK omNL1_isom) (omN_isom hK omNL2_isom)⟩

@[expose] def omNUSK : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) :=
  ⟨omGL K omNUS omNUS omNUS_sq, by
    rw [← omGL_commutator omNS1 omNS1 omNS2 omNS2 omNUS omNUS omNS1_sq omNS2_sq omNUS_sq
      omNUS_eq]
    exact commutator_mem_statedOmega (omN_isom hK omNS1_isom) (omN_isom hK omNS2_isom)⟩

@[expose] def omNHLK : StatedOmega (StatedQuadPlus 3 K) :=
  ⟨omGL K omNHL omNHL omNHL_sq, by
    rw [← omGL_commutator omNE3 omNE3 omNE4 omNE4 omNHL omNHL omNE3_sq omNE4_sq omNHL_sq
      omNHL_eq]
    exact commutator_mem_statedOmega (omP6_isom hK omNE3_isom) (omP6_isom hK omNE4_isom)⟩

@[expose] def omNHSK : StatedOmega (StatedQuadPlus 3 K) :=
  ⟨omGL K omNHS omNHS omNHS_sq, by
    rw [← omGL_commutator omNE1 omNE1 omNE2 omNE2 omNHS omNHS omNE1_sq omNE2_sq omNHS_sq
      omNHS_eq]
    exact commutator_mem_statedOmega (omP6_isom hK omNE1_isom) (omP6_isom hK omNE2_isom)⟩

theorem omNT_mul_TiK : omMat K omNT * omMat K omNTi = 1 := by
  rw [← omMat_mul, omNT_mul_Ti, omMat_one]

theorem omNTi_mul_TK : omMat K omNTi * omMat K omNT = 1 := by
  rw [← omMat_mul, omNTi_mul_T, omMat_one]

include hK in
theorem omNT_quadK : ∀ w : omNI' → K, StatedQuadMinus (3 + 1) K 1 1 (omMat K omNT *ᵥ w) =
    omQP (w ∘ Sum.inl) + StatedQuadPlus 3 K (w ∘ Sum.inr) := by
  intro w
  obtain ⟨v, rfl⟩ := exists_omCast_comp hK w
  rw [omMat_mulVec, statedQuadMinus_omCast, omNT_quad, map_add, Function.comp_assoc,
    Function.comp_assoc, statedQuadPlus_omCast]
  congr 1
  simp [omQP]

theorem omNTi_xh_TK : omMat K omNTi * ((omNXhK hK : GL omNI K) : Matrix omNI omNI K) *
    omMat K omNT = fromBlocks omXi 0 0 1 := by
  change omMat K omNTi * omMat K omNXh * omMat K omNT = _
  rw [← omMat_mul, ← omMat_mul, omNTi_xh_T, omMat_fromBlocks, omXi_omMat, omMat_one, omMat_zero',
    omMat_zero']

theorem perfectCore_centralizer_omNXhK :
    perfectCore (centralizer ({omNXhK hK} : Set (StatedOmega (StatedQuadMinus (3 + 1) K 1 1)))) =
      (omEps0 (Q₈ := StatedQuadMinus (3 + 1) K 1 1) (QP := omQP) (Q₆ := StatedQuadPlus 3 K)
        omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK)).range :=
  perfectCore_centralizer_omOrth omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK) (omNTi_xh_TK hK)
    commutator_statedOmega_quadPlus_three_any

theorem omEps0_omNHLK :
    omEps0 (Q₈ := StatedQuadMinus (3 + 1) K 1 1) (QP := omQP) (Q₆ := StatedQuadPlus 3 K)
      omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK) (omNHLK hK) = omNULK hK := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omEps0, coe_omEps]
  change omMat K omNT * fromBlocks 1 0 0 (omMat K omNHL) * omMat K omNTi = omMat K omNUL
  rw [← omMat_fromBlocks_one, ← omMat_mul, ← omMat_mul, omNT_hL_Ti]

theorem omEps0_omNHSK :
    omEps0 (Q₈ := StatedQuadMinus (3 + 1) K 1 1) (QP := omQP) (Q₆ := StatedQuadPlus 3 K)
      omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK) (omNHSK hK) = omNUSK hK := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omEps0, coe_omEps]
  change omMat K omNT * fromBlocks 1 0 0 (omMat K omNHS) * omMat K omNTi = omMat K omNUS
  rw [← omMat_fromBlocks_one, ← omMat_mul, ← omMat_mul, omNT_hS_Ti]

end Minus

section Lifts

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
  (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)

theorem kOmMVec_omCast : kOmMVec K 3 = omCast K ∘ kOmMVec (ZMod 2) 3 := by
  funext a
  simp only [Function.comp_apply, SymplecticPilot.kOmMVec, Pi.single_apply]
  split_ifs <;> simp

include hK in
theorem q2OmMIota_eq_of_res (g : StatedSp 3 K) (A : StatedOmega (StatedQuadMinus (3 + 1) K 1 1))
    (hfix : ((A : GL omNI K) : Matrix omNI omNI K) *ᵥ kOmMVec K 3 = kOmMVec K 3)
    (hres : ((A : GL omNI K) : Matrix omNI omNI K).submatrix (kOmMEmb 3) (kOmMEmb 3) =
      mat 3 K g) :
    q2OmMIota (k := K) (r := 3) le_rfl hirr hK g = A := by
  have hA : A ∈ fixedSubgroup (kOmMBetaC K 3 1 1) :=
    (SymplecticPilot.mem_fixedSubgroup_kOmMBetaC_iff K le_rfl hirr A).2 hfix
  obtain ⟨y, hy, hyg⟩ :=
    SymplecticPilot.kOmMFixRes_q2OmMIota (k := K) (r := 3) le_rfl hirr hK g
  have hyA : y = ⟨A, hA⟩ := by
    apply SymplecticPilot.kOmMFixRes_injective_two K le_rfl hirr hK
    rw [hyg]
    apply mat_injective
    rw [mat_apply (x := SymplecticPilot.kOmMFixRes K _ _ _), SymplecticPilot.coe_kOmMFixRes]
    exact hres.symm
  rw [← hy, hyA]

theorem q2OmMIota_nsElt :
    q2OmMIota (k := K) (r := 3) le_rfl hirr hK (nsElt 0) = omNXhK hK := by
  refine q2OmMIota_eq_of_res hK hirr _ _ ?_ ?_
  · change omMat K omNXh *ᵥ kOmMVec K 3 = kOmMVec K 3
    rw [kOmMVec_omCast, omMat_mulVec, omNXh_mulVec_vec]
  · change (omNXh.submatrix (kOmMEmb 3) (kOmMEmb 3)).map (omCast K) = mat 3 K (nsElt 0)
    rw [mat_nsElt, omNXh_submatrix, blockMat_omMat, zThreeMat_omMat]

theorem q2OmMIota_eltL :
    q2OmMIota (k := K) (r := 3) le_rfl hirr hK (elt (.positiveLong 1) 1) = omNULK hK := by
  refine q2OmMIota_eq_of_res hK hirr _ _ ?_ ?_
  · change omMat K omNUL *ᵥ kOmMVec K 3 = kOmMVec K 3
    rw [kOmMVec_omCast, omMat_mulVec, omNUL_mulVec_vec]
  · change (omNUL.submatrix (kOmMEmb 3) (kOmMEmb 3)).map (omCast K) = _
    rw [omNUL_submatrix, mat_elt_positiveLong]
    exact omMat_one_add_single _ _

theorem q2OmMIota_eltS :
    q2OmMIota (k := K) (r := 3) le_rfl hirr hK (elt (.positiveSum 1 2 (by decide)) 1) =
      omNUSK hK := by
  refine q2OmMIota_eq_of_res hK hirr _ _ ?_ ?_
  · change omMat K omNUS *ᵥ kOmMVec K 3 = kOmMVec K 3
    rw [kOmMVec_omCast, omMat_mulVec, omNUS_mulVec_vec]
  · change (omNUS.submatrix (kOmMEmb 3) (kOmMEmb 3)).map (omCast K) = _
    rw [omNUS_submatrix, mat_elt, one_smul]
    change (1 + (single _ _ (1 : ZMod 2) + single _ _ 1)).map (omCast K) = _
    rw [Matrix.map_add _ (map_add (omCast K)), Matrix.map_add _ (map_add (omCast K)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, Matrix.map_single, map_one]
    rfl

end Lifts

@[expose] def OmSixPlusCentValues : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
    Nat.card (centralizer ({omNHLK hK} : Set (StatedOmega (StatedQuadPlus 3 K)))) = 96 ∧
      Nat.card (centralizer ({omNHSK hK} : Set (StatedOmega (StatedQuadPlus 3 K)))) = 192

theorem eq_one_of_irreducible_two {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hc : c = 1 := by
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK c with h | h
    · exact absurd (by rw [h]; ring) (hirr 0)
    · exact h
  refine ⟨?_, hc⟩
  rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK b with h | h
  · exfalso
    apply hirr 1
    rw [h, hc, one_pow, zero_mul, add_zero, CharTwo.add_self_eq_zero]
  · exact h

theorem twoOmegaMinusModelValues_of_six (h6 : OmSixPlusCentValues) :
    TwoOmegaMinusModelValues := by
  intro K _ _ _ hK b c hirr
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible_two hK hirr
  have hcore : centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map
      (q2OmMIota (k := K) (r := 3) le_rfl hirr hK)) =
      (omEps0 (Q₈ := StatedQuadMinus (3 + 1) K 1 1) (QP := omQP) (Q₆ := StatedQuadPlus 3 K)
        omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK)).range := by
    rw [centralizerPerfectCore_def, SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers,
      centralizer_zpowers_om, q2OmMIota_nsElt hK hirr, perfectCore_centralizer_omNXhK hK]
  have hinj := omEps0_injective (Q₈ := StatedQuadMinus (3 + 1) K 1 1) (QP := omQP)
    (Q₆ := StatedQuadPlus 3 K) omNT_mul_TiK omNTi_mul_TK (omNT_quadK hK)
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [hcore, natCard_range_of_injective hinj, natCard_statedOmega_quadPlus_three_any, hK]
    decide
  · rw [centralizer_map_rootGroup_eq hK _ stdVec_positiveLong_one, hcore, q2OmMIota_eltL hK hirr,
      ← omEps0_omNHLK hK, card_centralizer_singleton_inf_range hinj, (h6 K hK).1]
    rfl
  · rw [centralizer_map_rootGroup_eq hK _ stdVec_positiveSum_one_two, hcore,
      q2OmMIota_eltS hK hirr, ← omEps0_omNHSK hK, card_centralizer_singleton_inf_range hinj,
      (h6 K hK).2]
    rfl

end CFSG.SeitzReduction.F4Pilot
