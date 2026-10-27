module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5K
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsGraph
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.SL44

open Matrix Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs
open scoped MatrixGroups

abbrev OI : Subgroup SL(4, F4) := fixSub (stdSL 4 F4 1 1 1)

theorem inv_transpose_of_mem_OI {y : SL(4, F4)} (hy : y ∈ OI) :
    ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)ᵀ = y := by
  have h := congrArg (fun z : SL(4, F4) => (z : Matrix (Fin 4) (Fin 4) F4)) (mem_fixSub.1 hy)
  simp only [stdSL_one_one_coe, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one] at h
  exact h

theorem transpose_mul_of_mem_OI {y : SL(4, F4)} (hy : y ∈ OI) :
    (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * y = 1 ∧
      (y : Matrix (Fin 4) (Fin 4) F4) * (y : Matrix _ _ F4)ᵀ = 1 := by
  have h := inv_transpose_of_mem_OI hy
  have ht : (y : Matrix (Fin 4) (Fin 4) F4)ᵀ =
      ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) := by
    rw [← h, transpose_transpose]
  rw [ht]
  exact ⟨congrArg Subtype.val (inv_mul_cancel y), congrArg Subtype.val (mul_inv_cancel y)⟩

theorem sum_sq_char_two (f : Fin 4 → F4) : (∑ i, f i) * (∑ i, f i) = ∑ i, f i * f i := by
  have := sum_pow_char (p := 2) (R := F4) Finset.univ f
  simpa [sq] using this

theorem col_sum_of_mem_OI {y : SL(4, F4)} (hy : y ∈ OI) (j : Fin 4) :
    ∑ i, (y : Matrix (Fin 4) (Fin 4) F4) i j = 1 := by
  have h := congrFun (congrFun (transpose_mul_of_mem_OI hy).1 j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [transpose_apply] at h
  rw [← sum_sq_char_two] at h
  exact eq_one_of_sq_eq_one_of_charTwo h

theorem row_sum_of_mem_OI {y : SL(4, F4)} (hy : y ∈ OI) (i : Fin 4) :
    ∑ j, (y : Matrix (Fin 4) (Fin 4) F4) i j = 1 := by
  have h := congrFun (congrFun (transpose_mul_of_mem_OI hy).2 i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [transpose_apply] at h
  rw [← sum_sq_char_two] at h
  exact eq_one_of_sq_eq_one_of_charTwo h

@[expose] def flagP : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 1, 0, 0; 1, 1, 1, 0; 1, 0, 1, 0; 1, 0, 0, 1]

@[expose] def flagQ : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 1, 1, 0; 0, 1, 1, 0; 1, 1, 0, 0; 1, 1, 1, 1]

theorem flagQ_mul_flagP : flagQ * flagP = 1 := by decide

theorem flagP_mul_flagQ : flagP * flagQ = 1 := by decide

@[expose] def flagM (y : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4 :=
  flagQ * (y : Matrix (Fin 4) (Fin 4) F4) * flagP

theorem flagM_mul (y y' : SL(4, F4)) : flagM (y * y') = flagM y * flagM y' := by
  simp only [flagM]
  calc flagQ * ((y : Matrix (Fin 4) (Fin 4) F4) * y') * flagP
      = flagQ * y * (flagP * flagQ) * y' * flagP := by rw [flagP_mul_flagQ]; simp [Matrix.mul_assoc]
    _ = flagQ * y * flagP * (flagQ * y' * flagP) := by simp only [Matrix.mul_assoc]

theorem flagM_injective {y y' : SL(4, F4)} (h : flagM y = flagM y') : y = y' := by
  apply Subtype.ext
  have e : ∀ z : SL(4, F4), (z : Matrix (Fin 4) (Fin 4) F4) = flagP * flagM z * flagQ := fun z => by
    simp only [flagM, ← Matrix.mul_assoc, flagP_mul_flagQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, flagP_mul_flagQ, Matrix.mul_one]
  rw [e y, e y', h]

theorem flagM_col_zero {y : SL(4, F4)} (hy : y ∈ OI) (i : Fin 4) :
    flagM y i 0 = (Pi.single 0 1 : Fin 4 → F4) i := by
  have he : (y : Matrix (Fin 4) (Fin 4) F4) *ᵥ (fun _ => 1) = fun _ => 1 := by
    funext k
    simp only [mulVec, dotProduct, mul_one]
    exact row_sum_of_mem_OI hy k
  have h1 : flagP *ᵥ Pi.single 0 1 = fun _ => 1 := by decide
  have h2 : flagQ *ᵥ (fun _ => 1) = Pi.single 0 1 := by decide
  have h3 : flagM y *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [flagM, ← mulVec_mulVec, ← mulVec_mulVec, h1, he, h2]
  have h4 := congrFun h3 i
  rwa [mulVec_single_one] at h4

theorem flagM_row_three {y : SL(4, F4)} (hy : y ∈ OI) (j : Fin 4) :
    flagM y 3 j = (Pi.single 3 1 : Fin 4 → F4) j := by
  have he : (fun _ => 1) ᵥ* (y : Matrix (Fin 4) (Fin 4) F4) = fun _ => 1 := by
    funext k
    simp only [vecMul, dotProduct, one_mul]
    exact col_sum_of_mem_OI hy k
  have h1 : Pi.single 3 1 ᵥ* flagQ = fun _ => 1 := by decide
  have h2 : (fun _ => 1) ᵥ* flagP = Pi.single 3 1 := by decide
  have h3 : Pi.single 3 1 ᵥ* flagM y = Pi.single 3 1 := by
    rw [flagM, ← vecMul_vecMul, ← vecMul_vecMul, h1, he, h2]
  have h4 := congrFun h3 j
  rwa [single_one_vecMul] at h4

theorem det_of_shape (M : Matrix (Fin 4) (Fin 4) F4)
    (h0 : ∀ i, M i 0 = (Pi.single 0 1 : Fin 4 → F4) i)
    (h3 : ∀ j, M 3 j = (Pi.single 3 1 : Fin 4 → F4) j) :
    M.det = M 1 1 * M 2 2 - M 1 2 * M 2 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_four]
  simp only [h0, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, h3, Fin.succ]

@[expose] def blk (y : SL(4, F4)) : Matrix (Fin 2) (Fin 2) F4 :=
  !![flagM y 1 1, flagM y 1 2; flagM y 2 1, flagM y 2 2]

theorem det_blk {y : SL(4, F4)} (hy : y ∈ OI) : (blk y).det = 1 := by
  have h := det_of_shape (flagM y) (flagM_col_zero hy) (flagM_row_three hy)
  have h1 : (flagM y).det = 1 := by
    rw [flagM, det_mul, det_mul, y.2, mul_one, ← det_mul, flagQ_mul_flagP, det_one]
  rw [blk, Matrix.det_fin_two_of, ← h, h1]

theorem blk_mul {y y' : SL(4, F4)} (hy : y ∈ OI) (hy' : y' ∈ OI) :
    blk (y * y') = blk y * blk y' := by
  have h0 := flagM_col_zero hy
  have h3 := flagM_row_three hy'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, flagM_mul, Matrix.mul_apply, Fin.sum_univ_four, h0, h3]

@[expose] def blkHom : OI →* SL(2, F4) where
  toFun y := ⟨blk y, det_blk y.2⟩
  map_one' := by
    apply Subtype.ext
    change blk 1 = 1
    have : flagM 1 = 1 := by simp [flagM, flagQ_mul_flagP]
    simp only [blk, this]
    decide
  map_mul' y y' := Subtype.ext (blk_mul y.2 y'.2)

@[expose] def unip (a b c d e : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, a, b, c; 0, 1, 0, d; 0, 0, 1, e; 0, 0, 0, 1]

theorem unip_mul_self (a b c d e : F4) :
    unip a b c d e * unip a b c d e = unip 0 0 (a * d + b * e) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unip, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem unip_zero_mul_self (c : F4) : unip 0 0 c 0 0 * unip 0 0 c 0 0 = 1 := by
  revert c
  decide

theorem pow_four_of_mem_ker {y : OI} (hy : y ∈ blkHom.ker) : y ^ 4 = 1 := by
  have hb : blk y = 1 := congrArg Subtype.val hy
  have h0 := flagM_col_zero y.2
  have h3 := flagM_row_three y.2
  have hu : flagM y = unip (flagM y 0 1) (flagM y 0 2) (flagM y 0 3) (flagM y 1 3)
      (flagM y 2 3) := by
    have e11 : flagM y 1 1 = 1 := by simpa [blk] using congrFun (congrFun hb 0) 0
    have e12 : flagM y 1 2 = 0 := by simpa [blk] using congrFun (congrFun hb 0) 1
    have e21 : flagM y 2 1 = 0 := by simpa [blk] using congrFun (congrFun hb 1) 0
    have e22 : flagM y 2 2 = 1 := by simpa [blk] using congrFun (congrFun hb 1) 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unip, h0, h3, e11, e12, e21, e22]
  apply Subtype.ext
  apply flagM_injective
  have h4 : flagM ((y : SL(4, F4)) ^ 4) = flagM 1 := by
    have e4 : (y : SL(4, F4)) ^ 4 = y * y * (y * y) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e4, flagM_mul, flagM_mul, hu, unip_mul_self, unip_zero_mul_self]
    simp [flagM, flagQ_mul_flagP]
  simpa using h4

theorem card_SL_two_F4 : Nat.card SL(2, F4) = 60 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    Nat.card_eq_fintype_card, F4.card]
  decide

theorem not_nine_dvd_card_OI : ¬ 9 ∣ Nat.card OI := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 blkHom.ker := fun y => ⟨2, by
    apply Subtype.ext
    simpa using pow_four_of_mem_ker y.2⟩
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hcard := Subgroup.card_ker_mul_card_range blkHom
  have hr : Nat.card blkHom.range ∣ 60 := card_SL_two_F4 ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk] at hcard
  intro h9
  rw [← hcard] at h9
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h9r : 9 ∣ Nat.card blkHom.range := hcop.dvd_of_dvd_mul_left h9
  exact absurd (h9r.trans hr) (by norm_num)

abbrev J₂ : Matrix (Fin 4) (Fin 4) F4 :=
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 4 2

abbrev ε4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := graphSumEquiv (show 2 + 2 = 4 from rfl)

abbrev re4 : Matrix (Fin 4) (Fin 4) F4 ≃+* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4 :=
  Matrix.reindexRingEquiv F4 ε4.symm

theorem re4_apply (M : Matrix (Fin 4) (Fin 4) F4) : re4 M = reindex ε4.symm ε4.symm M := rfl

theorem re4_transpose (M : Matrix (Fin 4) (Fin 4) F4) : re4 Mᵀ = (re4 M)ᵀ := by
  rw [re4_apply, re4_apply, transpose_reindex]

theorem re4_J₂ : re4 J₂ = fromBlocks 0 1 (-1) 0 := by
  have h := reindex_fromBlocks_swap (F := F4) (show 2 + 2 = 4 from rfl)
  rw [re4_apply, J₂, ← h, CharTwo.neg_eq]
  ext i j
  simp

theorem J₂_mul_self : J₂ * J₂ = 1 :=
  blockSwapJ_mul_blockSwapJ (show 2 + 2 = 4 from rfl)

theorem mem_fixSub_symplectic_iff {C : GL (Fin 4) F4}
    (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) {y : SL(4, F4)} :
    y ∈ fixSub (stdSL 4 F4 C 1 1) ↔ (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * J₂ * y = J₂ := by
  have hCi : ((C⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) = J₂ := by
    have hCC : C * C = 1 := Units.ext (by rw [Units.val_mul, hC, J₂_mul_self]; rfl)
    rw [inv_eq_of_mul_eq_one_right hCC, hC]
  constructor
  · intro hy
    have h := congrArg (fun z : SL(4, F4) => (z : Matrix (Fin 4) (Fin 4) F4)) (mem_fixSub.1 hy)
    simp only [stdSL_one_one_coe, hCi] at h
    rw [hC] at h
    have hyy : (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)ᵀ =
        1 := by
      rw [← transpose_mul]
      have : ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) * y = 1 :=
        congrArg Subtype.val (inv_mul_cancel y)
      rw [this, transpose_one]
    calc (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * J₂ * y
        = (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * J₂ *
            (J₂ * ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)ᵀ * J₂) := by rw [h]
      _ = (y : Matrix (Fin 4) (Fin 4) F4)ᵀ * (J₂ * J₂) *
            ((y⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)ᵀ * J₂ := by
          simp only [Matrix.mul_assoc]
      _ = J₂ := by rw [J₂_mul_self, Matrix.mul_one, hyy, Matrix.one_mul]
  · intro hy
    rw [mem_fixSub]
    exact stdSL_one_one_eq_self C (by rw [hCi]; exact hy)

theorem det_eq_one_of_mem_statedSp {A : GL (Fin 2 ⊕ Fin 2) F4}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F4) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4).det = 1 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff] at hA
  have h := congrArg Matrix.det hA
  rw [det_mul, det_mul, det_transpose] at h
  have hΩ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4).det = 1 := by
    rw [← re4_J₂, re4_apply, det_reindex_self]
    decide
  rw [hΩ, mul_one] at h
  exact eq_one_of_sq_eq_one_of_charTwo h

abbrev re4GL : SL(4, F4) →* GL (Fin 2 ⊕ Fin 2) F4 :=
  (Units.map re4.toMonoidHom).comp Matrix.SpecialLinearGroup.toGL

theorem coe_re4GL (y : SL(4, F4)) :
    ((re4GL y : GL (Fin 2 ⊕ Fin 2) F4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4) =
      re4 (y : Matrix (Fin 4) (Fin 4) F4) := rfl

theorem re4GL_mem {C : GL (Fin 4) F4} (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂)
    {y : SL(4, F4)} (hy : y ∈ fixSub (stdSL 4 F4 C 1 1)) :
    re4GL y ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F4 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_re4GL,
    ← re4_J₂, ← re4_transpose, ← map_mul, ← map_mul, (mem_fixSub_symplectic_iff hC).1 hy]

abbrev spHom {C : GL (Fin 4) F4} (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) :
    fixSub (stdSL 4 F4 C 1 1) →* CFSG.Assembly.LowTwoRank.StatedSp 2 F4 :=
  (re4GL.comp (fixSub (stdSL 4 F4 C 1 1)).subtype).codRestrict _ fun y => re4GL_mem hC y.2

theorem spHom_bijective {C : GL (Fin 4) F4} (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) :
    Function.Bijective (spHom hC) := by
  refine ⟨fun y y' h => ?_, fun A => ?_⟩
  · have h1 : re4 ((y : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) =
        re4 ((y' : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) := by
      rw [← coe_re4GL, ← coe_re4GL]
      exact congrArg (fun z : CFSG.Assembly.LowTwoRank.StatedSp 2 F4 =>
        ((z : GL (Fin 2 ⊕ Fin 2) F4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4)) h
    exact Subtype.ext (Subtype.ext (re4.injective h1))
  · set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4 :=
      ((A : GL (Fin 2 ⊕ Fin 2) F4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4) with hM
    have hdet : (re4.symm M).det = 1 := by
      have e : re4.symm M = reindex ε4 ε4 M := rfl
      rw [e, det_reindex_self]
      exact det_eq_one_of_mem_statedSp A.2
    set y : SL(4, F4) := ⟨re4.symm M, hdet⟩ with hydef
    have hyM : re4 (y : Matrix (Fin 4) (Fin 4) F4) = M := RingEquiv.apply_symm_apply re4 M
    have hy : y ∈ fixSub (stdSL 4 F4 C 1 1) := by
      rw [mem_fixSub_symplectic_iff hC]
      apply re4.injective
      have hA := (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff).1 A.2
      rw [map_mul, map_mul, re4_transpose, hyM, re4_J₂]
      exact hA
    refine ⟨⟨y, hy⟩, Subtype.ext (Units.ext ?_)⟩
    exact hyM

@[expose] def spEquiv {C : GL (Fin 4) F4} (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) :
    fixSub (stdSL 4 F4 C 1 1) ≃* CFSG.Assembly.LowTwoRank.StatedSp 2 F4 :=
  MulEquiv.ofBijective (spHom hC) (spHom_bijective hC)

theorem lieModel_fixSub_symplectic {C : GL (Fin 4) F4}
    (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) :
    CFSG.Blueprint.LieModel (fixSub (stdSL 4 F4 C 1 1)) .PSp 2 2 2 :=
  CFSG.SeitzReduction.SymplecticPilot.lieModel_of_mulEquiv_statedSp (spEquiv hC)
    (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num) le_rfl (by decide)

@[expose] def w₀Mat : Matrix (Fin 4) (Fin 4) F4 :=
  !![F4.ω, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

@[expose] def w₀InvMat : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, F4.ω, 0; 0, 0, 0, 1]

@[expose] def w₀ : SL(4, F4) :=
  ⟨w₀Mat, by simp [w₀Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide⟩

theorem w₀_mem {C : GL (Fin 4) F4}
    (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) :
    w₀ ∈ fixSub (stdSL 4 F4 C 1 1) :=
  (mem_fixSub_symplectic_iff hC).2 (by decide)

theorem trace_w₀ :
    (w₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω ∧
      ((w₀⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω := by
  rw [coe_inv_eq (M := w₀InvMat) (by decide)]
  decide

theorem not_forall_sigmaSL_eq_conj {C : GL (Fin 4) F4}
    (hC : (C : Matrix (Fin 4) (Fin 4) F4) = J₂) (H : GL (Fin 4) F4)
    (g : SL(4, F4)) :
    ¬ ∀ w ∈ (fixSub (stdSL 4 F4 C 1 1)).map (stdSL 4 F4 H 1 0).toMonoidHom,
      CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4 w = g * w * g⁻¹ := by
  intro h
  have hw := h _ ⟨w₀, w₀_mem hC, rfl⟩
  have h1 := congrArg (fun z : SL(4, F4) => (z : Matrix (Fin 4) (Fin 4) F4).trace) hw
  rw [hasTrType_sigmaSL, twist_one] at h1
  have hc := hasTrType_stdSL H 1 (ε := 0) zero_le_one
  have hgc : ∀ z : SL(4, F4), ((g * z * g⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4).trace =
      (z : Matrix (Fin 4) (Fin 4) F4).trace := fun z => by
    change ((g : Matrix (Fin 4) (Fin 4) F4) * z *
      ((g⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)).trace = _
    rw [Matrix.trace_mul_cycle, show ((g⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) * g = 1 from
      congrArg Subtype.val (inv_mul_cancel g), Matrix.one_mul]
  rw [hgc, MulEquiv.coe_toMonoidHom, hc, twist_zero, ← map_inv, hc, twist_zero] at h1
  simp only [RingAut.one_apply] at h1
  rw [trace_w₀.1, trace_w₀.2, barEquiv_apply] at h1
  exact absurd h1 (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.SL44
