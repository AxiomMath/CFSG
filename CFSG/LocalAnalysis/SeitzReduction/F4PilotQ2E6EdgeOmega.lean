module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeMat
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParamMinus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.LieType.Chevalley.C2E6Overlap TauCeti.GLSymplecticFin
open CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (E mat mat_apply mat_injective elt mat_elt)
open CFSG.SeitzReduction.SymplecticPilot (kOmMEmb kOmMVec kOmMEmb_injective q2OmMIota)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL mat_leviEmbedSL)

section Klein

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def edgeCast : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

theorem edgeCast_injective : Function.Injective (edgeCast K) :=
  (edgeCast K).injective

variable (K) in
@[expose] noncomputable def edgePK : Matrix EdgeV EdgeW K :=
  edgeP.map (edgeCast K)

variable (K) in
@[expose] noncomputable def edgePinvK : Matrix EdgeW EdgeV K :=
  edgePinv.map (edgeCast K)

theorem edgeCast_map_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    (1 : Matrix ι ι (ZMod 2)).map (edgeCast K) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem edgePK_mul_edgePinvK : edgePK K * edgePinvK K = 1 := by
  rw [edgePK, edgePinvK, ← Matrix.map_mul, edgeP_mul_edgePinv, edgeCast_map_one]

theorem edgePinvK_mul_edgePK : edgePinvK K * edgePK K = 1 := by
  rw [edgePK, edgePinvK, ← Matrix.map_mul, edgePinv_mul_edgeP, edgeCast_map_one]

theorem statedQuadMinus_edgePK_mulVec (w : EdgeW → K) :
    StatedQuadMinus (3 + 1) K 1 1 (edgePK K *ᵥ w) =
      pfSigned (fun i => w (Sum.inl i)) +
        (w (.inr 0) ^ 2 + w (.inr 0) * w (.inr 1) + w (.inr 1) ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [StatedQuadMinus, pfSigned, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.map_apply, edgePK, edgeP, edgeMat,
    Matrix.of_apply]
  simp
  linear_combination (3 * w (.inl 1) * w (.inl 4) + w (.inl 1) * w (.inr 0) +
    2 * w (.inl 1) * w (.inr 1) + 2 * w (.inl 1) ^ 2 + w (.inl 4) * w (.inr 0) +
    w (.inl 4) * w (.inr 1) + w (.inl 4) ^ 2) * h2

variable (K) in
@[expose] noncomputable def edgeDK (A : Matrix (Fin 4) (Fin 4) K) : Matrix EdgeW EdgeW K :=
  fromBlocks (ext2 A) 0 0 1

variable (K) in
@[expose] noncomputable def edgeMuK (A : Matrix (Fin 4) (Fin 4) K) : Matrix EdgeV EdgeV K :=
  edgePK K * edgeDK K A * edgePinvK K

theorem edgeDK_mul (A B : Matrix (Fin 4) (Fin 4) K) :
    edgeDK K (A * B) = edgeDK K A * edgeDK K B := by
  rw [edgeDK, edgeDK, edgeDK, fromBlocks_multiply, ext2_mul]
  simp

theorem edgeMuK_mul (A B : Matrix (Fin 4) (Fin 4) K) :
    edgeMuK K (A * B) = edgeMuK K A * edgeMuK K B := by
  have h : edgePK K * edgeDK K A * edgePinvK K * (edgePK K * edgeDK K B * edgePinvK K) =
      edgePK K * edgeDK K A * (edgePinvK K * edgePK K) * edgeDK K B * edgePinvK K := by
    simp only [Matrix.mul_assoc]
  rw [edgeMuK, edgeMuK, edgeMuK, h, edgePinvK_mul_edgePK, Matrix.mul_one, edgeDK_mul]
  simp only [Matrix.mul_assoc]

theorem edgeMuK_one : edgeMuK K 1 = 1 := by
  rw [edgeMuK, edgeDK, ext2_one, fromBlocks_one, Matrix.mul_one, edgePK_mul_edgePinvK]

theorem edgeMuK_map (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    edgeMuK K (A.map (edgeCast K)) = (edgeMu A).map (edgeCast K) := by
  rw [edgeMuK, edgeMu, edgeDK, edgeD, ext2_map, Matrix.map_mul, Matrix.map_mul, fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), edgeCast_map_one]
  rfl

theorem statedQuadMinus_edgeMuK_mulVec {A : Matrix (Fin 4) (Fin 4) K} (hA : A.det = 1)
    (v : EdgeV → K) :
    StatedQuadMinus (3 + 1) K 1 1 (edgeMuK K A *ᵥ v) = StatedQuadMinus (3 + 1) K 1 1 v := by
  set w := edgePinvK K *ᵥ v with hw
  have hv : v = edgePK K *ᵥ w := by
    rw [hw, Matrix.mulVec_mulVec, edgePK_mul_edgePinvK, Matrix.one_mulVec]
  have hμ : edgeMuK K A *ᵥ v = edgePK K *ᵥ (edgeDK K A *ᵥ w) := by
    rw [edgeMuK, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h1 : (fun i => (edgeDK K A *ᵥ w) (Sum.inl i)) = ext2 A *ᵥ fun j => w (Sum.inl j) := by
    funext i
    simp [edgeDK, fromBlocks_mulVec, Function.comp_def]
  have h2 : ∀ i, (edgeDK K A *ᵥ w) (Sum.inr i) = w (Sum.inr i) := by
    intro i
    simp [edgeDK, fromBlocks_mulVec]
  rw [hμ, statedQuadMinus_edgePK_mulVec, h1, h2, h2, pfSigned_ext2, hA, one_mul, hv,
    statedQuadMinus_edgePK_mulVec]

variable (K) in
@[expose] noncomputable def edgeMuMon : SpecialLinearGroup (Fin 4) K →* Matrix EdgeV EdgeV K where
  toFun A := edgeMuK K A
  map_one' := by simp [edgeMuK_one]
  map_mul' A B := by simp [edgeMuK_mul]

variable (K) in
@[expose] noncomputable def edgeMuGL : SpecialLinearGroup (Fin 4) K →* GL EdgeV K :=
  (edgeMuMon K).toHomUnits

theorem range_edgeMuGL_le :
    (edgeMuGL K).range ≤ StatedOmega (StatedQuadMinus (3 + 1) K 1 1) := by
  have hP : Group.IsPerfect (SpecialLinearGroup (Fin 4) K) :=
    LinearPilot.isPerfect_specialLinearGroup_of_three_le_card (Fin 4) (by simp)
  have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 4) K)), ⊤⁆ = ⊤ :=
    hP.commutator_eq_top
  have hle : Subgroup.map (edgeMuGL K) (⊤ : Subgroup (SpecialLinearGroup (Fin 4) K)) ≤
      Subgroup.closure {A : GL EdgeV K | ∀ v, StatedQuadMinus (3 + 1) K 1 1
        ((A : Matrix EdgeV EdgeV K) *ᵥ v) = StatedQuadMinus (3 + 1) K 1 1 v} := by
    rintro _ ⟨A, -, rfl⟩
    exact Subgroup.subset_closure (statedQuadMinus_edgeMuK_mulVec A.2)
  rw [MonoidHom.range_eq_map, ← hperf, Subgroup.map_commutator, StatedOmega]
  exact Subgroup.commutator_mono hle hle

variable (K) in
@[expose] noncomputable def edgeMuOm :
    SpecialLinearGroup (Fin 4) K →* StatedOmega (StatedQuadMinus (3 + 1) K 1 1) :=
  (edgeMuGL K).codRestrict _ fun A => range_edgeMuGL_le ⟨A, rfl⟩

theorem coe_edgeMuOm (A : SpecialLinearGroup (Fin 4) K) :
    (((edgeMuOm K A : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) :
      Matrix EdgeV EdgeV K) = edgeMuK K A :=
  rfl

theorem coe_transvection_eq_map {i j : Fin 4} (hij : i ≠ j) :
    ((SpecialLinearGroup.transvection hij (1 : K) : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (edgeT i j).map (edgeCast K) := by
  rw [SpecialLinearGroup.transvection_coe, edgeT, Matrix.map_add _ (map_add _), edgeCast_map_one,
    Matrix.map_single, map_one]

theorem coe_edgeMuOm_transvection {i j : Fin 4} (hij : i ≠ j) :
    (((edgeMuOm K (SpecialLinearGroup.transvection hij 1) :
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      (edgeMu (edgeT i j)).map (edgeCast K) := by
  rw [coe_edgeMuOm, coe_transvection_eq_map, edgeMuK_map]

theorem coe_edgeMuOm_transvection_mul {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) :
    (((edgeMuOm K (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hkl 1) :
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      (edgeMu (edgeT i j * edgeT k l)).map (edgeCast K) := by
  rw [coe_edgeMuOm]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_transvection_eq_map, coe_transvection_eq_map, ← Matrix.map_mul, edgeMuK_map]

end Klein

section Inj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_mem_center_SL4_two (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin 4) K}
    (hg : g ∈ center (SpecialLinearGroup (Fin 4) K)) : g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  have hr1 : r = 1 := by
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK r with h | h
    · rw [h, Fintype.card_fin, zero_pow (by norm_num)] at hr
      exact absurd hr zero_ne_one
    · exact h
  apply Subtype.ext
  rw [← hrg, hr1, map_one]
  rfl

theorem isSimpleGroup_SL4_two (hK : Nat.card K = 2) :
    IsSimpleGroup (SpecialLinearGroup (Fin 4) K) := by
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 4) (by norm_num)
    (Or.inl (by norm_num))).2.1
  have hc : center (SpecialLinearGroup (Fin 4) K) = ⊥ :=
    eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (eq_one_of_mem_center_SL4_two hK hg)
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

theorem edgeMu_t02_ne_one : edgeMu (edgeT 0 2) ≠ 1 := by decide +kernel

theorem edgeMuOm_injective (hK : Nat.card K = 2) : Function.Injective (edgeMuOm K) := by
  have := isSimpleGroup_SL4_two hK
  rcases (edgeMuOm K).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    have hmem : SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 2 by decide) (1 : K) ∈
        (edgeMuOm K).ker := by
      rw [h]
      exact Subgroup.mem_top _
    have h1 := congrArg (fun A : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) =>
      ((A : GL EdgeV K) : Matrix EdgeV EdgeV K)) (MonoidHom.mem_ker.1 hmem)
    simp only [coe_edgeMuOm_transvection, OneMemClass.coe_one, Units.val_one] at h1
    apply edgeMu_t02_ne_one
    apply Matrix.map_injective (edgeCast_injective (K := K))
    change (edgeMu (edgeT 0 2)).map (edgeCast K) =
      (1 : Matrix EdgeV EdgeV (ZMod 2)).map (edgeCast K)
    rw [h1, edgeCast_map_one]

end Inj

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
  (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)

include hK hirr in
theorem q2OmMIota_eq_of_mulVec (A : StatedOmega (StatedQuadMinus (3 + 1) K 1 1))
    (hv : ((A : GL EdgeV K) : Matrix EdgeV EdgeV K) *ᵥ kOmMVec K 3 = kOmMVec K 3)
    {s : StatedSp 3 K}
    (hs : ((A : GL EdgeV K) : Matrix EdgeV EdgeV K).submatrix (kOmMEmb 3) (kOmMEmb 3) =
      mat 3 K s) :
    q2OmMIota le_rfl hirr hK s = A := by
  have hfix : A ∈ fixedSubgroup (SymplecticPilot.kOmMBetaC K 3 1 1) :=
    (SymplecticPilot.mem_fixedSubgroup_kOmMBetaC_iff K le_rfl hirr A).2 hv
  have hres : SymplecticPilot.kOmMFixRes K le_rfl hirr ⟨A, hfix⟩ = s := by
    apply mat_injective
    rw [mat_apply, SymplecticPilot.coe_kOmMFixRes]
    exact hs
  rw [q2OmMIota, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (MulEquiv.symm_apply_eq _).2 hres.symm]
  rfl

omit [Finite K] in
theorem coordEmbedMat_kOmMEmb_mulVec_vec (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    coordEmbedMat (kOmMEmb 3) g *ᵥ kOmMVec K 3 = kOmMVec K 3 := by
  funext a
  by_cases ha : a ∈ Set.range (kOmMEmb 3)
  · obtain ⟨z, rfl⟩ := ha
    have h1 := congrFun (coordEmbedMat_mulVec_comp kOmMEmb_injective g (kOmMVec K 3)) z
    simp only [Function.comp_apply] at h1
    rw [h1, SymplecticPilot.kOmMVec_kOmMEmb]
    have h0 : (kOmMVec K 3 ∘ kOmMEmb 3) = 0 :=
      funext fun w => SymplecticPilot.kOmMVec_kOmMEmb K w
    rw [h0, Matrix.mulVec_zero, Pi.zero_apply]
  · exact coordEmbedMat_mulVec_of_not_mem _ _ ha

omit [Finite K] [CharP K 2] in
theorem coordEmbedMat_kOmMEmb_submatrix (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    (coordEmbedMat (kOmMEmb 3) g).submatrix (kOmMEmb 3) (kOmMEmb 3) = g := by
  ext x y
  exact coordEmbedMat_apply_image kOmMEmb_injective g x y

omit [Finite K] [CharP K 2] in
theorem coordEmbedGL_leviEmbedSL_mem (C : SpecialLinearGroup (Fin 3) K) :
    coordEmbedGL (kOmMEmb 3) kOmMEmb_injective
        ((leviEmbedSL K 3 C : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) ∈
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1) := by
  have hyS : leviEmbedSL K 3 C ∈ SymplecticPilot.siegelBlock K (Finset.univ : Finset (Fin 3)) :=
    ⟨C, by rw [LinearPilot.blockSpecialLinear_univ]; exact Subgroup.mem_top _, rfl⟩
  have hyO := SymplecticPilot.siegelBlockGL_le_statedOmega_of_three_le (F := K)
    (B := (Finset.univ : Finset (Fin 3))) (by simp) ⟨_, hyS, rfl⟩
  exact (SymplecticPilot.kOmM_isCoordSplit_hyp 3 (1 : K) 1).map_statedOmega_le kOmMEmb_injective
    ⟨_, hyO, rfl⟩

include hK hirr in
theorem coe_q2OmMIota_leviEmbedSL (C : SpecialLinearGroup (Fin 3) K) :
    (((q2OmMIota le_rfl hirr hK (leviEmbedSL K 3 C) :
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      coordEmbedMat (kOmMEmb 3) (mat 3 K (leviEmbedSL K 3 C)) := by
  rw [q2OmMIota_eq_of_mulVec hK hirr ⟨_, coordEmbedGL_leviEmbedSL_mem C⟩
    (coordEmbedMat_kOmMEmb_mulVec_vec _) (coordEmbedMat_kOmMEmb_submatrix _)]
  rfl

end Iota

section Explicit

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def edgeSL3 (C₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : C₀.det = 1) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨C₀.map (edgeCast K), by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_one]⟩

theorem mat_leviEmbedSL_edgeSL3 {C₀ D₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : C₀.det = 1)
    (hCD : C₀ * D₀ᵀ = 1) :
    mat 3 K (leviEmbedSL K 3 (edgeSL3 K C₀ h)) = (edgeLev C₀ D₀).map (edgeCast K) := by
  set A := edgeSL3 K C₀ h with hA
  have h1 : (A : Matrix (Fin 3) (Fin 3) K) * (D₀.map (edgeCast K))ᵀ = 1 := by
    change C₀.map (edgeCast K) * (D₀.map (edgeCast K))ᵀ = 1
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hCD, edgeCast_map_one]
  have h2 : ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul, A.2, one_smul]
  have h3 : ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (D₀.map (edgeCast K))ᵀ := by
    calc ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((A : Matrix (Fin 3) (Fin 3) K) * (D₀.map (edgeCast K))ᵀ) := by rw [h1, Matrix.mul_one]
      _ = (D₀.map (edgeCast K))ᵀ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [mat_leviEmbedSL, h3, Matrix.transpose_transpose, edgeLev, fromBlocks_map]
  simp only [Matrix.map_zero _ (map_zero (edgeCast K))]
  rfl

theorem coordEmbedMat_edgeLev (C₀ D₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    coordEmbedMat (kOmMEmb 3) ((edgeLev C₀ D₀).map (edgeCast K)) =
      (edgeSg C₀ D₀).map (edgeCast K) := by
  have hn : ∀ (j : Fin 2) (x : Fin 3 ⊕ Fin 3), kOmMEmb 3 x ≠ Sum.inr (Sum.inr j) :=
    fun j x => SymplecticPilot.kOmMEmb_ne_tail x j
  have himg : ∀ x y : Fin 3 ⊕ Fin 3, coordEmbedMat (kOmMEmb 3)
      ((edgeLev C₀ D₀).map (edgeCast K)) (kOmMEmb 3 x) (kOmMEmb 3 y) =
        (edgeLev C₀ D₀).map (edgeCast K) x y :=
    fun x y => coordEmbedMat_apply_image kOmMEmb_injective _ x y
  have hnot : ∀ (a b : EdgeV), (∃ j, a = Sum.inr (Sum.inr j)) ∨ (∃ j, b = Sum.inr (Sum.inr j)) →
      coordEmbedMat (kOmMEmb 3) ((edgeLev C₀ D₀).map (edgeCast K)) a b =
        (1 : Matrix EdgeV EdgeV K) a b := by
    intro a b hab
    refine coordEmbedMat_apply_of_not_mem _ fun h => ?_
    rcases hab with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨x, hx⟩ := h.1
      exact hn j x hx
    · obtain ⟨x, hx⟩ := h.2
      exact hn j x hx
  ext a b
  rcases a with i | i | i <;> rcases b with j | j | j
  · exact himg (Sum.inl i) (Sum.inl j)
  · exact (himg (Sum.inl i) (Sum.inr j)).trans (by simp [edgeLev, edgeSg])
  · rw [hnot _ _ (Or.inr ⟨j, rfl⟩)]
    simp [edgeSg]
  · exact (himg (Sum.inr i) (Sum.inl j)).trans (by simp [edgeLev, edgeSg])
  · exact himg (Sum.inr i) (Sum.inr j)
  · rw [hnot _ _ (Or.inr ⟨j, rfl⟩)]
    simp [edgeSg]
  · rw [hnot _ _ (Or.inl ⟨i, rfl⟩)]
    simp [edgeSg]
  · rw [hnot _ _ (Or.inl ⟨i, rfl⟩)]
    simp [edgeSg]
  · rw [hnot _ _ (Or.inl ⟨i, rfl⟩)]
    by_cases hij : i = j
    · subst hij
      simp [edgeSg]
    · simp [edgeSg, hij, Matrix.one_apply_ne (show (Sum.inr (Sum.inr i) : EdgeV) ≠
        Sum.inr (Sum.inr j) from fun h => hij (Sum.inr_injective (Sum.inr_injective h)))]

theorem edgeE_map (r : RootSubgroupIndex 3) : (E (ZMod 2) r).map (edgeCast K) = E K r := by
  cases r <;> simp [E, Matrix.map_sub, Matrix.map_add]

theorem mat_elt_one (r : RootSubgroupIndex 3) :
    mat 3 K (elt r (1 : K)) = (edgeSp r).map (edgeCast K) := by
  rw [mat_elt, one_smul, edgeSp, Matrix.map_add _ (map_add _), edgeCast_map_one, edgeE_map]

theorem kOmMVec_eq_comp : kOmMVec K 3 = edgeCast K ∘ edgeVec := by
  funext a
  simp only [SymplecticPilot.kOmMVec, edgeVec, Function.comp_apply, Pi.single_apply]
  split_ifs <;> simp

theorem map_mulVec_kOmMVec {M : Matrix EdgeV EdgeV (ZMod 2)} (h : M *ᵥ edgeVec = edgeVec) :
    M.map (edgeCast K) *ᵥ kOmMVec K 3 = kOmMVec K 3 := by
  funext a
  rw [kOmMVec_eq_comp, ← RingHom.map_mulVec, h, Function.comp_apply]

end Explicit

section Values

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
  (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)

include hK hirr in
theorem q2OmMIota_elt_eq_edgeMuOm {r : RootSubgroupIndex 3} {A : SpecialLinearGroup (Fin 4) K}
    {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hA : (((edgeMuOm K A : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) :
      Matrix EdgeV EdgeV K) = (edgeMu A₀).map (edgeCast K))
    (hv : edgeMu A₀ *ᵥ edgeVec = edgeVec)
    (hs : (edgeMu A₀).submatrix (kOmMEmb 3) (kOmMEmb 3) = edgeSp r) :
    q2OmMIota le_rfl hirr hK (elt r 1) = edgeMuOm K A := by
  refine q2OmMIota_eq_of_mulVec hK hirr _ ?_ ?_
  · rw [hA]
    exact map_mulVec_kOmMVec hv
  · rw [hA, Matrix.submatrix_map, hs, mat_elt_one]

include hK hirr in
theorem q2OmMIota_P12 : q2OmMIota le_rfl hirr hK (elt (.positiveSum 1 2 (by decide)) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 2 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection _) edgeMu_t02_vec
    edgeMu_t02_hyp

include hK hirr in
theorem q2OmMIota_M12 : q2OmMIota le_rfl hirr hK (elt (.negativeSum 1 2 (by decide)) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 0 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection _) edgeMu_t20_vec
    edgeMu_t20_hyp

include hK hirr in
theorem q2OmMIota_D12 : q2OmMIota le_rfl hirr hK (elt (.difference 1 2 (by decide)) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 3 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection _) edgeMu_t13_vec
    edgeMu_t13_hyp

include hK hirr in
theorem q2OmMIota_D21 : q2OmMIota le_rfl hirr hK (elt (.difference 2 1 (by decide)) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 1 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection _) edgeMu_t31_vec
    edgeMu_t31_hyp

include hK hirr in
theorem q2OmMIota_L1 : q2OmMIota le_rfl hirr hK (elt (.positiveLong 1) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 3 by decide) 1 *
      SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 2 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection_mul _ _)
    edgeMu_plus_vec edgeMu_plus_hyp

include hK hirr in
theorem q2OmMIota_N1 : q2OmMIota le_rfl hirr hK (elt (.negativeLong 1) 1) =
    edgeMuOm K (SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 1 by decide) 1 *
      SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 0 by decide) 1) :=
  q2OmMIota_elt_eq_edgeMuOm hK hirr (coe_edgeMuOm_transvection_mul _ _)
    edgeMu_minus_vec edgeMu_minus_hyp

include hK hirr in
theorem coe_q2OmMIota_edgeSL3 {C₀ D₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : C₀.det = 1)
    (hCD : C₀ * D₀ᵀ = 1) :
    (((q2OmMIota le_rfl hirr hK (leviEmbedSL K 3 (edgeSL3 K C₀ h)) :
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      (edgeSg C₀ D₀).map (edgeCast K) := by
  rw [coe_q2OmMIota_leviEmbedSL hK hirr, mat_leviEmbedSL_edgeSL3 h hCD, coordEmbedMat_edgeLev]

noncomputable abbrev edgePi (K : Type) [Field K] [CharP K 2] : StatedSp 3 K :=
  leviEmbedSL K 3 (edgeSL3 K edgeS01 det_edgeS01)

noncomputable abbrev edgePi' (K : Type) [Field K] [CharP K 2] : StatedSp 3 K :=
  leviEmbedSL K 3 (edgeSL3 K edgeS02 det_edgeS02)

omit [Finite K] in
theorem elt_cPrime_eq : elt (.positiveLong 0) (1 : K) * elt (.negativeLong 0) 1 =
    edgePi K * elt (.positiveLong 1) 1 * elt (.negativeLong 1) 1 * edgePi K := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, mat_leviEmbedSL_edgeSL3 det_edgeS01 edgeS01_mul_transpose]
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, edgeSp_c_eq]

include hK hirr in
theorem coe_q2OmMIota_cPrime :
    (((q2OmMIota le_rfl hirr hK (elt (.positiveLong 0) 1 * elt (.negativeLong 0) 1) :
      StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      (edgeP * (fromBlocks (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 0 edgeC :
        Matrix EdgeW EdgeW (ZMod 2)) * edgePinv).map (edgeCast K) := by
  rw [elt_cPrime_eq, map_mul, map_mul, map_mul, q2OmMIota_L1 hK hirr, q2OmMIota_N1 hK hirr]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_q2OmMIota_edgeSL3 hK hirr det_edgeS01 edgeS01_mul_transpose,
    coe_edgeMuOm_transvection_mul, coe_edgeMuOm_transvection_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, edgeMc_eq]

include hK hirr in
theorem commute_q2OmMIota_cPrime_edgeMuOm (A : SpecialLinearGroup (Fin 4) K) :
    Commute (q2OmMIota le_rfl hirr hK (elt (.positiveLong 0) 1 * elt (.negativeLong 0) 1))
      (edgeMuOm K A) := by
  set Ck : Matrix EdgeW EdgeW K :=
    fromBlocks (1 : Matrix (Fin 6) (Fin 6) K) 0 0 (edgeC.map (edgeCast K)) with hCk
  have hC : (edgeP * (fromBlocks (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 0 edgeC :
      Matrix EdgeW EdgeW (ZMod 2)) * edgePinv).map (edgeCast K) =
      edgePK K * Ck * edgePinvK K := by
    rw [Matrix.map_mul, Matrix.map_mul, fromBlocks_map, edgeCast_map_one,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rfl
  have hblk : Ck * edgeDK K A = edgeDK K A * Ck := by
    rw [hCk, edgeDK, fromBlocks_multiply, fromBlocks_multiply]
    simp
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_q2OmMIota_cPrime hK hirr, coe_edgeMuOm, hC, edgeMuK]
  calc edgePK K * Ck * edgePinvK K * (edgePK K * edgeDK K A * edgePinvK K)
      = edgePK K * (Ck * (edgePinvK K * edgePK K) * edgeDK K A) * edgePinvK K := by
        simp only [Matrix.mul_assoc]
    _ = edgePK K * (edgeDK K A * (edgePinvK K * edgePK K) * Ck) * edgePinvK K := by
        rw [edgePinvK_mul_edgePK, Matrix.mul_one, Matrix.mul_one, hblk]
    _ = edgePK K * edgeDK K A * edgePinvK K * (edgePK K * Ck * edgePinvK K) := by
        simp only [Matrix.mul_assoc]

omit [Finite K] in
theorem elt_relay_eq : elt (.difference 0 1 (by decide)) (1 : K) *
      elt (.negativeSum 0 1 (by decide)) 1 =
    leviEmbedSL K 3 (edgeSL3 K edgeC01 det_edgeC01) *
      (edgePi' K * elt (.negativeSum 1 2 (by decide)) 1 * edgePi' K) := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, mat_leviEmbedSL_edgeSL3 det_edgeC01 edgeC01_mul_transpose,
    mat_leviEmbedSL_edgeSL3 det_edgeS02 edgeS02_mul_transpose]
  rw [edgeSp_D01_eq, edgeSp_M01_eq]
  simp only [Matrix.map_mul]

omit [Finite K] in
theorem elt_relay'_eq : elt (.difference 1 0 (by decide)) (1 : K) *
      elt (.positiveSum 0 1 (by decide)) 1 =
    leviEmbedSL K 3 (edgeSL3 K edgeC10 det_edgeC10) *
      (edgePi' K * elt (.positiveSum 1 2 (by decide)) 1 * edgePi' K) := by
  apply mat_injective
  simp only [map_mul, mat_elt_one, mat_leviEmbedSL_edgeSL3 det_edgeC10 edgeC10_mul_transpose,
    mat_leviEmbedSL_edgeSL3 det_edgeS02 edgeS02_mul_transpose]
  rw [edgeSp_D10_eq, edgeSp_P01_eq]
  simp only [Matrix.map_mul]

include hK hirr in
theorem coe_q2OmMIota_relay :
    (((q2OmMIota le_rfl hirr hK (elt (.difference 0 1 (by decide)) 1 *
      elt (.negativeSum 0 1 (by decide)) 1) :
        StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      edgeRu.map (edgeCast K) := by
  rw [elt_relay_eq, map_mul, map_mul, map_mul, q2OmMIota_M12 hK hirr]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_q2OmMIota_edgeSL3 hK hirr det_edgeC01 edgeC01_mul_transpose,
    coe_q2OmMIota_edgeSL3 hK hirr det_edgeS02 edgeS02_mul_transpose, coe_edgeMuOm_transvection,
    edgeRu]
  simp only [Matrix.map_mul, Matrix.mul_assoc]

include hK hirr in
theorem coe_q2OmMIota_relay' :
    (((q2OmMIota le_rfl hirr hK (elt (.difference 1 0 (by decide)) 1 *
      elt (.positiveSum 0 1 (by decide)) 1) :
        StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : GL EdgeV K) : Matrix EdgeV EdgeV K) =
      edgeRu'.map (edgeCast K) := by
  rw [elt_relay'_eq, map_mul, map_mul, map_mul, q2OmMIota_P12 hK hirr]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_q2OmMIota_edgeSL3 hK hirr det_edgeC10 edgeC10_mul_transpose,
    coe_q2OmMIota_edgeSL3 hK hirr det_edgeS02 edgeS02_mul_transpose, coe_edgeMuOm_transvection,
    edgeRu']
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem commute_of_coe_map {x y : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)}
    {X Y : Matrix EdgeV EdgeV (ZMod 2)}
    (hx : ((x : GL EdgeV K) : Matrix EdgeV EdgeV K) = X.map (edgeCast K))
    (hy : ((y : GL EdgeV K) : Matrix EdgeV EdgeV K) = Y.map (edgeCast K)) (h : X * Y = Y * X) :
    Commute x y := by
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hx, hy, ← Matrix.map_mul, ← Matrix.map_mul, h]

include hK hirr in
theorem commute_q2OmMIota_relay_t01 :
    Commute (q2OmMIota le_rfl hirr hK (elt (.difference 0 1 (by decide)) 1 *
      elt (.negativeSum 0 1 (by decide)) 1))
      (edgeMuOm K (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) 1)) :=
  commute_of_coe_map (coe_q2OmMIota_relay hK hirr) (coe_edgeMuOm_transvection _)
    edgeRu_commute_t01

include hK hirr in
theorem commute_q2OmMIota_relay_t10 :
    Commute (q2OmMIota le_rfl hirr hK (elt (.difference 0 1 (by decide)) 1 *
      elt (.negativeSum 0 1 (by decide)) 1))
      (edgeMuOm K (SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) 1)) :=
  commute_of_coe_map (coe_q2OmMIota_relay hK hirr) (coe_edgeMuOm_transvection _)
    edgeRu_commute_t10

include hK hirr in
theorem commute_q2OmMIota_relay'_t01 :
    Commute (q2OmMIota le_rfl hirr hK (elt (.difference 1 0 (by decide)) 1 *
      elt (.positiveSum 0 1 (by decide)) 1))
      (edgeMuOm K (SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) 1)) :=
  commute_of_coe_map (coe_q2OmMIota_relay' hK hirr) (coe_edgeMuOm_transvection _)
    edgeRu'_commute_t01

include hK hirr in
theorem commute_q2OmMIota_relay'_t10 :
    Commute (q2OmMIota le_rfl hirr hK (elt (.difference 1 0 (by decide)) 1 *
      elt (.positiveSum 0 1 (by decide)) 1))
      (edgeMuOm K (SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) 1)) :=
  commute_of_coe_map (coe_q2OmMIota_relay' hK hirr) (coe_edgeMuOm_transvection _)
    edgeRu'_commute_t10

end Values

end CFSG.SeitzReduction.F4Pilot
