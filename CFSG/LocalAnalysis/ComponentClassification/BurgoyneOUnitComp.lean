module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem unitaryFieldData_EAlg {c : K} [Fact (Irreducible (sqPoly c))] (hc : c ≠ 0) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) : UnitaryFieldData p f (EAlg c) := by
  refine ⟨hp, ?_, ?_⟩
  · by_contra h
    have hf : f = 0 := by omega
    rw [hf, pow_zero] at hKc
    have := Finite.one_lt_card (α := K)
    omega
  · rw [card_EAlg hc, hKc, ← pow_mul, mul_comm]

theorem transpose_phiE_mul_wNeg (hK : ringChar K ≠ 2) {c : K} [Fact (Irreducible (sqPoly c))]
    (hc : ¬ IsSquare c) (x : EAlg c) :
    (phiE c x)ᵀ * wMat 1 (-c) = wMat 1 (-c) * phiE c (x ^ Nat.card K) := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b : K, x = algebraMap K (EAlg c) a +
      algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c) := ⟨_, _, eq_add_root hc0 x⟩
  rw [pow_card_add_root hK hc, phiE_add_root, phiE_add_root]
  exact transpose_mul_wNeg c a b

omit [Finite K] in
theorem wMat_inv_mul {c : K} (hc : c ≠ 0) : wMat 1 (-c⁻¹) * wMat 1 (-c) = 1 := by
  rw [wMat, wMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [hc]

theorem commutator_uGrp_eq_unitarySU {p f : ℕ} {E : Type} [Field E] [Finite E] [Fact p.Prime]
    [CharP E p] (h : UnitaryFieldData p f E) {n : ℕ} (hn : 3 ≤ n) (hq : p ^ f ≠ 2) :
    ⁅uGrp h.bar (1 : Matrix (Fin n) (Fin n) E), uGrp h.bar (1 : Matrix (Fin n) (Fin n) E)⁆ =
      unitarySU p f E n := by
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := p)
    (f := f) (by rw [h.card, ← pow_mul, mul_comm]) hn (fun e => hq (Prod.ext_iff.1 e).2)).1
  have hle : unitarySU p f E n ≤ uGrp h.bar (1 : Matrix (Fin n) (Fin n) E) := by
    intro x hx
    rw [mem_unitarySU_iff h] at hx
    rw [mem_uGrp, Matrix.mul_one]
    exact hx.2
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]
    · have hm : ⁅a, b⁆ ∈ uGrp h.bar (1 : Matrix (Fin n) (Fin n) E) :=
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      rw [mem_uGrp, Matrix.mul_one] at hm
      exact hm
  · have e : ⁅unitarySU p f E n, unitarySU p f E n⁆ = unitarySU p f E n :=
      PSL.commutator_eq_self_of_isQuasisimple hqs
    rw [← e]
    exact commutator_mono hle hle

theorem compData_unit (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) {n : ℕ} (hn : 3 ≤ n) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    CompData ⁅isoCent R A, isoCent R A⁆ := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hc⟩
  have h := unitaryFieldData_EAlg hc0 hp hKc
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (EAlg c) := h.finite
  have : CharP (EAlg c) p := h.charP
  have hσ : ∀ x : EAlg c, h.bar x = x ^ Nat.card K := fun x => by rw [h.bar_apply, hKc]
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 (-c) =
      wMat 1 (-c) * (phiE c).toRingHom (h.bar x) := fun x => by
    rw [hσ]
    exact transpose_phiE_mul_wNeg hK hc x
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-c)) * resMat (phiE c).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom) (σ := h.bar)
    (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c) (wMat_inv_mul hc0) hW (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) 1 hRG hA
  have hq : p ^ f ≠ 2 := by
    rw [← hKc]
    intro h2
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    rw [h2] at this
    exact (by decide : ¬ Odd 2) this
  rw [hZ, commutator_uGrp_eq_unitarySU h hn hq]
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := EAlg c)
    (p := p) (f := f) (by rw [h.card, ← pow_mul, mul_comm]) hn
    (fun e => hq (Prod.ext_iff.1 e).2)).1
  exact (CompData.of_isQuasisimple hqs).map (resGL_injective (phiE_injective c) n)

end CFSG.ComponentClassification.Burgoyne.O
