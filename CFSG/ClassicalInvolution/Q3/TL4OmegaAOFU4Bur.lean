module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU4Aut
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFInn
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4Twin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U4

open Matrix CFSG.ClassicalInvolution.Q3.Q3MFOU4 CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalInvolution.Phan
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (exists_sq_eq_of_norm_eq_one)
open CFSG.ComponentClassification.Burgoyne.B (upaired_oddCoreIn_eq_bot_three)
open scoped MatrixGroups

section Model

theorem ufd9 : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [card_F9, ← pow_mul, mul_comm]⟩

theorem bar_eq_σ9 (c : F9) : ufd9.bar c = σ9 c := by
  rw [UnitaryFieldData.bar_apply, σ9_apply, pow_one]

theorem map_bar_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F9) : M.map ufd9.bar = M.map σ9 := by
  ext i j
  exact bar_eq_σ9 _

theorem map_barEq_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F9) :
    M.map (barEq ufd9) = M.map σ9 := by
  ext i j
  exact bar_eq_σ9 _

@[expose] noncomputable def suStated : Su F9 3 1 4 ≃* StatedSU 4 (3 ^ 1) F9 :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU card_F9 4)

theorem map_center_suStated :
    (Subgroup.center (Su F9 3 1 4)).map (suStated : Su F9 3 1 4 →* StatedSU 4 (3 ^ 1) F9) =
      (StatedScalars (Fin 4) F9).subgroupOf (StatedSU 4 (3 ^ 1) F9) := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, hu0, hu⟩ := scalar_of_mem_center hz
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Units.mk0 u hu0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    exact hu.symm
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨suStated.symm g, mem_center_of_scalar (c := (c : F9)) ?_, suStated.apply_symm_apply g⟩
    show ((g : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = _
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]

@[expose] noncomputable def psuStated :
    Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4) ≃* StatedProj (StatedSU 4 (3 ^ 1) F9) :=
  QuotientGroup.congr _ _ suStated map_center_suStated

theorem psuStated_mk (x : Su F9 3 1 4) :
    psuStated (QuotientGroup.mk x) = projH _ (suStated x) := rfl

theorem congr_psuStated (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)))
    (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    (A : uU ufd9 4) (φ : F9 ≃+* F9)
    (hα : ∀ x, suMat (α x) = ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) * (suMat x).map φ *
      (((A : GL (Fin 4) F9)⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) :
    MulAut.congr psuStated ρ = uConjAut ufd9 (by norm_num) A * uFieldAut ufd9 (by norm_num) φ := by
  ext y
  obtain ⟨x, rfl⟩ := (psuStated.surjective.comp QuotientGroup.mk_surjective) y
  rw [Function.comp_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, hρmk, psuStated_mk, psuStated_mk, uLift_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_uLift]
  exact hα x

theorem oddCoreIn_fixed_of_psuStated (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)))
    (h : oddCoreIn (fixedSubgroup (MulAut.congr psuStated ρ)) = ⊥) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' psuStated.symm _ h
  have h2 : MulAut.congr psuStated.symm (MulAut.congr psuStated ρ) = ρ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

theorem conj_injective_stated {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : StatedProj (StatedSU n (3 ^ 1) F9) →*
      MulAut (StatedProj (StatedSU n (3 ^ 1) F9))) :=
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_conj_inj_pu card_F9 hn fun e => by
    have := congrArg Prod.snd e
    norm_num at this

@[expose] noncomputable def uOf {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hgu : (G.map σ9)ᵀ * G = 1) : uU ufd9 4 :=
  ⟨⟨G, Gi, mul_eq_one_comm.mp hGiG, hGiG⟩, (mem_uU ufd9).2 (by
    show (G.map ufd9.bar)ᵀ * G = 1
    rw [map_bar_eq]
    exact hgu)⟩

end Model

section Orth

theorem psuOrthStatement_proved : PSUOrthStatement := by
  intro ρ α _ hρmk _ G Gi hGiG hα hgu hGG
  have hA := congr_psuStated ρ α hρmk (uOf hGiG hgu) (barEq ufd9) fun x => by
    rw [hα x, RingEquiv.mapMatrix_apply, ← map_barEq_eq]
    rfl
  have hinj := conj_injective_stated (by norm_num : 3 ≤ 4)
  have hAc : (((uOf hGiG hgu : uU ufd9 4) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
      (((uOf hGiG hgu : uU ufd9 4) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).map ufd9.bar =
        (1 : F9) • 1 := by
    show G * G.map ufd9.bar = (1 : F9) • 1
    rw [map_bar_eq, hGG, one_smul]
  have key := oddCoreIn_fixed_eq_bot_of_inn hinj _
    (graph_oddCoreIn_eq_bot ufd9 (by norm_num) (by norm_num) hinj le_rfl hAc)
  rw [← hA] at key
  exact oddCoreIn_fixed_of_psuStated ρ key

end Orth

section Paired

theorem oddCoreIn_fixed_paired {n : ℕ} (hn : 3 ≤ n) (A : uU ufd9 n) {c : F9}
    (hAA : ((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) *
      ((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) = c • 1)
    (hcc : c * c = -1) (hNc : σ9 c * c = 1) :
    oddCoreIn (fixedSubgroup (uConjAut ufd9 (by omega) A)) = ⊥ := by
  set M := ((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) with hM
  have h2 : (2 : F9) ≠ 0 := two_ne_zero_F9
  have hU : (M.map ufd9.bar)ᵀ * M = 1 := (mem_uU ufd9).1 A.2
  have hN : ufd9.norm c = 1 := by rw [UnitaryFieldData.norm, bar_eq_σ9, mul_comm c]; exact hNc
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one ufd9 (by norm_num) hN
  have hN1 : ufd9.norm l = -1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← hcc, ← hlc]
    ring
  have hAA' : M * M = (l ^ 2) • 1 := by rw [hAA, hlc]
  have hNi : ufd9.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm (ufd9.bar l) l, ← UnitaryFieldData.norm, hN1, inv_neg,
      inv_one]
  have hU' : ((l⁻¹ • M).map ufd9.bar)ᵀ * (l⁻¹ • M) = -1 := by
    rw [show (l⁻¹ • M).map ufd9.bar = ufd9.bar l⁻¹ • M.map ufd9.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨m, rfl⟩ := exists_half_of_antiunitary ufd9 h2 hU' hA'2
  have hm : 2 ≤ m := by omega
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form ufd9 h2 hU' hA'2 hl0 hN1
  set HG := uGL ufd9 Hm hHU with hHG
  have hHi : (((HG : GL (Fin (m + m)) F9)⁻¹ : GL (Fin (m + m)) F9) :
      Matrix (Fin (m + m)) (Fin (m + m)) F9) = (Hm.map ufd9.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (m + m)) F9)⁻¹ : GL (Fin (m + m)) F9) :
      Matrix (Fin (m + m)) (Fin (m + m)) F9) * M *
      ((HG : GL (Fin (m + m)) F9) : Matrix (Fin (m + m)) (Fin (m + m)) F9) =
        (1 : F9) • ((uPairA (m := m) ufd9 h2 hl0 hN1 : GL (Fin (m + m)) F9) :
          Matrix (Fin (m + m)) (Fin (m + m)) F9) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  set H : uU ufd9 (m + m) := ⟨HG, uGL_mem ufd9 _ _⟩ with hH
  have hT : (uConjAut ufd9 (by omega) H)⁻¹ * uConjAut ufd9 (by omega) A *
      uConjAut ufd9 (by omega) H = uConjAut ufd9 (by omega) (uPairA (m := m) ufd9 h2 hl0 hN1) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    refine uConjAut_eq_of_eq_smul ufd9 hn one_ne_zero ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hconj
  have hinj := conj_injective_stated hn
  have key := oddCoreIn_fixed_eq_bot_of_inn hinj _
    (upaired_oddCoreIn_eq_bot_three ufd9 (by norm_num) h2 hm (by norm_num) hinj le_rfl hl0 hN1)
  have h1 := oddCoreIn_fixed_conj_eq_bot (uConjAut ufd9 (by omega) H) _ key
  rw [← hT] at h1
  have e : uConjAut ufd9 (by omega) H * ((uConjAut ufd9 (by omega) H)⁻¹ *
      uConjAut ufd9 (by omega) A * uConjAut ufd9 (by omega) H) *
        (uConjAut ufd9 (by omega) H)⁻¹ = uConjAut ufd9 (by omega) A := by group
  rwa [e] at h1

theorem psuDiagStatement_proved : PSUDiagStatement := by
  intro ρ α _ hρmk _ G Gi hGiG hα hgu c hc hcc
  have hA := congr_psuStated ρ α hρmk (uOf hGiG hgu) 1 fun x => by
    rw [hα x, map_one_ringEquiv]
    rfl
  have hA' : MulAut.congr psuStated ρ = uConjAut ufd9 (by norm_num) (uOf hGiG hgu) := by
    rw [hA, map_one]
    exact mul_one _
  have key := oddCoreIn_fixed_paired (by norm_num : 3 ≤ 4) (uOf hGiG hgu) hc hcc
    (norm_of_sq hgu hc)
  rw [← hA'] at key
  exact oddCoreIn_fixed_of_psuStated ρ key

end Paired

section Final


theorem outerFixedOddFree_psu4 : OuterFixedOddFree .PSU 4 :=
  outerFixedOddFree_psu4_of psuDiagStatement_proved psuOrthStatement_proved

end Final

end CFSG.ClassicalInvolution.Q3.TL4.U4
