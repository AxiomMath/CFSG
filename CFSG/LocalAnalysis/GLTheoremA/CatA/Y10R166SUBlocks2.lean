module

public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocksBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary
open CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K]

@[expose] def suLineVec : Fin 6 → K := fun i => if i = 0 ∨ i = 1 then 1 else 0

@[expose] def suRadVec (m : Fin 6 → K) : Fin 6 → K :=
  fun i => if i = 2 ∨ i = 3 ∨ i = 4 then m i else 0

theorem suRadVec_add (m m' : Fin 6 → K) :
    suRadVec (m + m') = suRadVec m + suRadVec m' := by
  funext i
  simp only [suRadVec, Pi.add_apply]
  split_ifs <;> simp

@[expose] noncomputable def suRadCocycle (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) : K :=
  ∑ i, suRadVec m i * h.bar (suRadVec m i)

theorem suRadCocycle_bar (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) :
    h.bar (suRadCocycle h m) = suRadCocycle h m := by
  simp only [suRadCocycle, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem suRadCocycle_zero (h : UnitaryFieldData 2 f K) : suRadCocycle h 0 = 0 := by
  simp [suRadCocycle, suRadVec]

theorem suRadVec_zero : suRadVec (0 : Fin 6 → K) = 0 := by
  funext i; simp [suRadVec]

theorem suRadVec_bar_zero (h : UnitaryFieldData 2 f K) :
    suRadVec (fun i => h.bar ((0 : Fin 6 → K) i)) = 0 := by
  funext i; simp [suRadVec]

theorem suRadCocycle_add (h : UnitaryFieldData 2 f K) (m m' : Fin 6 → K) :
    suRadCocycle h (m + m') =
      suRadCocycle h m + suRadCocycle h m' +
        ((suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))) +
          (suRadVec (fun i => h.bar (m i)) ⬝ᵥ suRadVec m')) := by
  simp only [suRadCocycle, suRadVec, Pi.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib, dotProduct, Fin.sum_univ_six]
  simp
  ring

theorem suLineVec_dot_self (h : UnitaryFieldData 2 f K) :
    suLineVec (K := K) ⬝ᵥ suLineVec = 0 := by
  haveI : CharP K 2 := h.charP
  simp [dotProduct, suLineVec, Fin.sum_univ_six, CharTwo.add_self_eq_zero]

theorem suLineVec_dot_suRadVec (m : Fin 6 → K) :
    suLineVec (K := K) ⬝ᵥ suRadVec m = 0 := by
  simp [dotProduct, suLineVec, suRadVec, Fin.sum_univ_six]

theorem suRadVec_dot_suLineVec (m : Fin 6 → K) :
    suRadVec m ⬝ᵥ suLineVec (K := K) = 0 := by
  simp [dotProduct, suLineVec, suRadVec, Fin.sum_univ_six]

@[expose] noncomputable def unitaryRadMatrix (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K) :
    Matrix (Fin 6) (Fin 6) K :=
  1 + y • vecMulVec suLineVec suLineVec + vecMulVec suLineVec (suRadVec m) +
    vecMulVec (suRadVec (fun i => h.bar (m i))) suLineVec

theorem unitaryRadMatrix_mul (h : UnitaryFieldData 2 f K) (m m' : Fin 6 → K) (y y' : K) :
    unitaryRadMatrix h m y * unitaryRadMatrix h m' y' =
      unitaryRadMatrix h (m + m')
        (y + y' + (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i)))) := by
  haveI : CharP K 2 := h.charP
  have hVadd : vecMulVec suLineVec (suRadVec (m + m')) =
      vecMulVec suLineVec (suRadVec m) + vecMulVec suLineVec (suRadVec m') := by
    rw [suRadVec_add, vecMulVec_add]
  have hWadd : vecMulVec (suRadVec (fun i => h.bar ((m + m') i))) suLineVec =
      vecMulVec (suRadVec (fun i => h.bar (m i))) suLineVec +
        vecMulVec (suRadVec (fun i => h.bar (m' i))) suLineVec := by
    have hbar_add : (fun i => h.bar ((m + m') i)) =
        (fun i => h.bar (m i)) + fun i => h.bar (m' i) := by
      funext i; simp
    rw [hbar_add, suRadVec_add, add_vecMulVec]
  simp only [unitaryRadMatrix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec,
    suLineVec_dot_self h, suLineVec_dot_suRadVec, suRadVec_dot_suLineVec, hVadd, hWadd]
  simp only [smul_zero, zero_smul, mul_zero, zero_mul, mul_one, one_mul, vecMulVec_zero,
    zero_vecMulVec, vecMulVec_smul, add_smul]
  module


section Eichler

variable (h : UnitaryFieldData 2 f K)

noncomputable def suRadSig : K ≃+* K :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  CFSG.LieType.BorelTits.unitaryInvolution K 2 f

theorem suRadSig_apply (c : K) : suRadSig h c = h.bar c := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  rw [suRadSig, CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]

theorem suRadSig_invol (c : K) : suRadSig h (suRadSig h c) = c := by
  rw [suRadSig_apply, suRadSig_apply, h.bar_bar]

theorem suLineVec_sig (i : Fin 6) : suRadSig h (suLineVec i) = suLineVec i := by
  rw [suLineVec]
  split_ifs <;> simp [suRadSig_apply]

theorem neg_suLineVec (h : UnitaryFieldData 2 f K) :
    (-suLineVec : Fin 6 → K) = suLineVec := by
  haveI : CharP K 2 := h.charP
  funext i
  exact CharTwo.neg_eq (suLineVec i)

theorem unitaryRadMatrix_eq_eichlerMat (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K) :
    unitaryRadMatrix h m y =
      eichlerMat (suRadSig h) suLineVec
        (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) (h.bar y) := by
  haveI : CharP K 2 := h.charP
  have hc2 : (h.bar y) • (suLineVec : Fin 6 → K) + (h.bar y) • (suLineVec : Fin 6 → K) = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  have hsum : (h.bar y • (suLineVec : Fin 6 → K) + suRadVec (fun i => h.bar (m i))) +
      (h.bar y) • (suLineVec : Fin 6 → K) = suRadVec (fun i => h.bar (m i)) := by
    calc (h.bar y • (suLineVec : Fin 6 → K) + suRadVec (fun i => h.bar (m i))) +
          (h.bar y) • (suLineVec : Fin 6 → K)
        = (h.bar y • (suLineVec : Fin 6 → K) + (h.bar y) • (suLineVec : Fin 6 → K)) +
            suRadVec (fun i => h.bar (m i)) := by abel
      _ = 0 + suRadVec (fun i => h.bar (m i)) := by rw [hc2]
      _ = suRadVec (fun i => h.bar (m i)) := zero_add _
  have hsig_y : (fun i : Fin 6 => suRadSig h
        ((h.bar y • (suLineVec : Fin 6 → K) + suRadVec (fun j => h.bar (m j))) i)) =
      (fun i : Fin 6 => (y • (suLineVec : Fin 6 → K) + suRadVec m) i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [suRadSig_apply, map_add, map_mul]
    have hu : h.bar (suLineVec i) = suLineVec i := by
      by_cases hi : i = 0 ∨ i = 1 <;> simp [suLineVec, hi]
    have hv : h.bar (suRadVec (fun j => h.bar (m j)) i) = suRadVec m i := by
      by_cases hi : i = 2 ∨ i = 3 ∨ i = 4 <;> simp [suRadVec, hi, h.bar_bar]
    rw [h.bar_bar, hu, hv]
  have hsigU : (fun i => suRadSig h (suLineVec i)) = (suLineVec : Fin 6 → K) :=
    funext (suLineVec_sig h)
  rw [unitaryRadMatrix, eichlerMat, hsigU, neg_suLineVec h, hsum, hsig_y, vecMulVec_add,
    vecMulVec_smul]
  set W : Matrix (Fin 6) (Fin 6) K := vecMulVec (suRadVec (fun i => h.bar (m i))) suLineVec with hW
  set U : Matrix (Fin 6) (Fin 6) K := vecMulVec suLineVec suLineVec with hU
  set V : Matrix (Fin 6) (Fin 6) K := vecMulVec suLineVec (suRadVec m) with hV
  have hWU : W * U = 0 := by
    rw [hW, hU, vecMulVec_mul_vecMulVec, suLineVec_dot_self h, zero_smul, vecMulVec_zero]
  have hWV : W * V = 0 := by
    rw [hW, hV, vecMulVec_mul_vecMulVec, suLineVec_dot_self h, zero_smul, vecMulVec_zero]
  have hWP : W * (y • U + V) = 0 := by
    rw [mul_add, Matrix.mul_smul, hWU, hWV, smul_zero, add_zero]
  have h1 : (1 + W) * (1 + (y • U + V)) =
      1 + W + (y • U + V) + W * (y • U + V) := by
    simp only [mul_add, add_mul, mul_one, one_mul]
    abel
  have hexp : (1 + W) * (1 + (y • U + V)) = 1 + y • U + V + W := by
    rw [h1, hWP, add_zero]
    abel
  exact hexp.symm

theorem herm_suRadEichlerVec (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K) :
    herm (suRadSig h) (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i)))
        (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) =
      suRadCocycle h m := by
  haveI : CharP K 2 := h.charP
  simp only [herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    suRadSig_apply, h.bar_bar, suLineVec, suRadVec, suRadCocycle, Fin.sum_univ_six, Fin.isValue]
  norm_num
  simp only [h.bar_bar]
  rw [CharTwo.add_self_eq_zero, zero_add]

theorem herm_suLineVec_self (h : UnitaryFieldData 2 f K) :
    herm (suRadSig h) suLineVec suLineVec = 0 := by
  haveI : CharP K 2 := h.charP
  simp only [herm, suLineVec, suRadSig_apply, Fin.sum_univ_six, Fin.isValue]
  norm_num
  exact CharTwo.two_eq_zero

theorem herm_suLineVec_suRadEichlerVec (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K) :
    herm (suRadSig h) suLineVec
      (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) = 0 := by
  haveI : CharP K 2 := h.charP
  simp only [herm, suLineVec, suRadVec, suRadSig_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_six, Fin.isValue]
  norm_num
  exact CharTwo.add_self_eq_zero _

theorem unitaryRadMatrix_det (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K) :
    (unitaryRadMatrix h m y).det = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  rw [unitaryRadMatrix_eq_eichlerMat h m y]
  exact eichlerMat_det (suRadSig_invol h)
    (herm_suLineVec_self h) (herm_suLineVec_suRadEichlerVec h m y) (h.bar y)

theorem unitaryRadMatrix_unitary (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) {y : K}
    (hy : y + h.bar y = suRadCocycle h m) :
    ((unitaryRadMatrix h m y).map h.bar)ᵀ * unitaryRadMatrix h m y = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  rw [unitaryRadMatrix_eq_eichlerMat h m y]
  have he := herm_suLineVec_self h
  have hey := herm_suLineVec_suRadEichlerVec h m y
  have hc : h.bar y + suRadSig h (h.bar y) =
      -herm (suRadSig h) (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i)))
        (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) := by
    rw [herm_suRadEichlerVec, suRadSig_apply, h.bar_bar]
    rw [show -suRadCocycle h m = suRadCocycle h m from CharTwo.neg_eq _]
    rw [add_comm]
    exact hy
  have hiso : ∀ x x' : Fin 6 → K,
      herm (suRadSig h)
        (eichlerMat (suRadSig h) suLineVec
          (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) (h.bar y) *ᵥ x)
        (eichlerMat (suRadSig h) suLineVec
          (h.bar y • suLineVec + suRadVec (fun i => h.bar (m i))) (h.bar y) *ᵥ x') =
      herm (suRadSig h) x x' := by
    intro x x'
    rw [eichlerMat_mulVec he, eichlerMat_mulVec he]
    exact eichler_isometry (suRadSig_invol h) he hey hc x x'
  have hconj := conjTr_mul_self_of_isometry (σ := suRadSig h) hiso
  rw [conjTr] at hconj
  rwa [show (⇑(suRadSig h) : K → K) = ⇑h.bar from funext (suRadSig_apply h)] at hconj

end Eichler

@[expose] noncomputable def unitaryRadElem (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K)
    (hy : y + h.bar y = suRadCocycle h m) : unitarySU 2 f K 6 :=
  ofSL h ⟨unitaryRadMatrix h m y, unitaryRadMatrix_det h m y⟩
    (unitaryRadMatrix_unitary h m hy)

@[simp] theorem coe_unitaryRadElem (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) (y : K)
    (hy : y + h.bar y = suRadCocycle h m) :
    (((unitaryRadElem h m y hy : unitarySU 2 f K 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = unitaryRadMatrix h m y :=
  rfl


theorem suRadVec_dot_self_eq_cocycle (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) :
    suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m i)) = suRadCocycle h m := by
  simp only [dotProduct, suRadVec, suRadCocycle, Fin.sum_univ_six, Fin.isValue]
  norm_num

theorem suRadCocycle_bar_dot (h : UnitaryFieldData 2 f K) (m m' : Fin 6 → K) :
    h.bar (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))) =
      suRadVec (fun i => h.bar (m i)) ⬝ᵥ suRadVec m' := by
  simp only [dotProduct, suRadVec, map_sum, map_mul, Fin.sum_univ_six, Fin.isValue]
  norm_num
  simp only [h.bar_bar]

theorem suRadCocycle_add_self (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) {y : K}
    (hy : y + h.bar y = suRadCocycle h m) :
    (y + suRadCocycle h m) + h.bar (y + suRadCocycle h m) = suRadCocycle h m := by
  haveI : CharP K 2 := h.charP
  rw [map_add, suRadCocycle_bar]
  calc (y + suRadCocycle h m) + (h.bar y + suRadCocycle h m)
      = (y + h.bar y) + (suRadCocycle h m + suRadCocycle h m) := by abel
    _ = suRadCocycle h m + 0 := by rw [hy, CharTwo.add_self_eq_zero]
    _ = suRadCocycle h m := add_zero _

theorem suRadCocycle_self_add_bar (h : UnitaryFieldData 2 f K) (m : Fin 6 → K) :
    suRadCocycle h m + h.bar (suRadCocycle h m) = suRadCocycle h 0 := by
  haveI : CharP K 2 := h.charP
  rw [suRadCocycle_bar, suRadCocycle_zero]
  exact CharTwo.add_self_eq_zero _

@[expose] def unitaryLineRadical (h : UnitaryFieldData 2 f K) :
    Subgroup (unitarySU 2 f K 6) where
  carrier := {A | ∃ (m : Fin 6 → K) (y : K) (hy : y + h.bar y = suRadCocycle h m),
    A = unitaryRadElem h m y hy}
  one_mem' := by
    haveI : CharP K 2 := h.charP
    refine ⟨0, 0, ?_, ?_⟩
    · rw [suRadCocycle_zero]; simp
    · apply Subtype.ext
      apply Units.ext
      simp only [coe_unitaryRadElem, unitaryRadMatrix, OneMemClass.coe_one, Units.val_one]
      rw [suRadVec_zero, suRadVec_bar_zero h]
      simp
  mul_mem' := by
    haveI : CharP K 2 := h.charP
    rintro A B ⟨m, y, hy, rfl⟩ ⟨m', y', hy', rfl⟩
    refine ⟨m + m', y + y' + (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))),
      ?_, ?_⟩
    ·
      calc (y + y' + (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i)))) +
            h.bar (y + y' + (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))))
          = (y + h.bar y) + (y' + h.bar y') +
              ((suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))) +
                h.bar (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i)))) := by
            rw [map_add, map_add]; abel
        _ = suRadCocycle h m + suRadCocycle h m' +
              ((suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m' i))) +
                (suRadVec (fun i => h.bar (m i)) ⬝ᵥ suRadVec m')) := by
            rw [hy, hy', suRadCocycle_bar_dot]
        _ = suRadCocycle h (m + m') := by rw [suRadCocycle_add]
    ·
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryRadElem]
      rw [unitaryRadMatrix_mul]
  inv_mem' := by
    haveI : CharP K 2 := h.charP
    rintro A ⟨m, y, hy, rfl⟩
    refine ⟨m, y + suRadCocycle h m, suRadCocycle_add_self h m hy, ?_⟩
    have hprod : unitaryRadElem h m y hy *
        unitaryRadElem h m (y + suRadCocycle h m) (suRadCocycle_add_self h m hy) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryRadElem, OneMemClass.coe_one,
        Units.val_one]
      rw [unitaryRadMatrix_mul]
      have hm : m + m = (0 : Fin 6 → K) := by
        funext i; exact CharTwo.add_self_eq_zero _
      have hyy : y + (y + suRadCocycle h m) +
          (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m i))) = 0 := by
        rw [suRadVec_dot_self_eq_cocycle]
        calc y + (y + suRadCocycle h m) + suRadCocycle h m
            = (y + y) + (suRadCocycle h m + suRadCocycle h m) := by abel
          _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
      rw [hm, hyy]
      rw [unitaryRadMatrix, suRadVec_zero, suRadVec_bar_zero h]
      simp
    have hinv : (unitaryRadElem h m y hy)⁻¹ =
        unitaryRadElem h m (y + suRadCocycle h m) (suRadCocycle_add_self h m hy) := by
      apply mul_left_cancel (a := unitaryRadElem h m y hy)
      rw [mul_inv_cancel, hprod]
    exact hinv

theorem unitaryLineRadical_isPGroup (h : UnitaryFieldData 2 f K) :
    IsPGroup 2 (unitaryLineRadical h) := by
  haveI : CharP K 2 := h.charP
  intro g
  obtain ⟨m, y, hy, hg⟩ := g.2
  refine ⟨2, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, hg]
  have hsq : (unitaryRadElem h m y hy) * (unitaryRadElem h m y hy) =
      unitaryRadElem h 0 (suRadCocycle h m) (suRadCocycle_self_add_bar h m) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryRadElem, OneMemClass.coe_one,
      Units.val_one]
    rw [unitaryRadMatrix_mul]
    have hm : m + m = (0 : Fin 6 → K) := by
      funext i; exact CharTwo.add_self_eq_zero _
    have hyy : y + y + (suRadVec m ⬝ᵥ suRadVec (fun i => h.bar (m i))) =
        suRadCocycle h m := by
      rw [suRadVec_dot_self_eq_cocycle, CharTwo.add_self_eq_zero, zero_add]
    rw [hm, hyy]
  have hsq2 : (unitaryRadElem h 0 (suRadCocycle h m) (suRadCocycle_self_add_bar h m)) *
      (unitaryRadElem h 0 (suRadCocycle h m) (suRadCocycle_self_add_bar h m)) = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_unitaryRadElem, OneMemClass.coe_one,
      Units.val_one]
    rw [unitaryRadMatrix_mul]
    have hm : (0 : Fin 6 → K) + 0 = 0 := by simp
    have hyy : suRadCocycle h m + suRadCocycle h m +
        (suRadVec 0 ⬝ᵥ suRadVec (fun i => h.bar ((0 : Fin 6 → K) i))) = suRadCocycle h 0 := by
      rw [show (suRadVec 0 ⬝ᵥ suRadVec (fun i => h.bar ((0 : Fin 6 → K) i))) = suRadCocycle h 0 from
        suRadVec_dot_self_eq_cocycle h 0]
      rw [CharTwo.add_self_eq_zero, zero_add]
    rw [hm, hyy, suRadCocycle_zero]
    rw [unitaryRadMatrix, suRadVec_zero, suRadVec_bar_zero h]
    simp
  calc (unitaryRadElem h m y hy) ^ 2 ^ 2
      = ((unitaryRadElem h m y hy) * (unitaryRadElem h m y hy)) *
        ((unitaryRadElem h m y hy) * (unitaryRadElem h m y hy)) := by
        rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
    _ = (unitaryRadElem h 0 (suRadCocycle h m) (suRadCocycle_self_add_bar h m)) *
        (unitaryRadElem h 0 (suRadCocycle h m) (suRadCocycle_self_add_bar h m)) := by
      rw [hsq]
    _ = 1 := hsq2

theorem unitaryLineRadical_le_unitaryBlock (h : UnitaryFieldData 2 f K) :
    unitaryLineRadical h ≤ unitaryBlock h ((Finset.univ : Finset (Fin 6)).erase 5) := by
  rintro A ⟨m, y, hy, rfl⟩
  rw [mem_unitaryBlock]
  intro i j hij
  rw [coe_unitaryRadElem]
  have hi5 : i = (5 : Fin 6) ∨ j = (5 : Fin 6) := by
    by_contra hcon
    push Not at hcon
    have hi : i ∈ (Finset.univ : Finset (Fin 6)).erase 5 := by
      simp [Finset.mem_erase, hcon.1]
    have hj : j ∈ (Finset.univ : Finset (Fin 6)).erase 5 := by
      simp [Finset.mem_erase, hcon.2]
    exact (hij.elim (fun h => h hi) fun h => h hj)
  simp only [unitaryRadMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, suLineVec, suRadVec, smul_eq_mul]
  rcases hi5 with rfl | rfl <;> simp

end CFSG.LocalAnalysis.GLTheoremA.Y10F
