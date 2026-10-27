module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL orthComponentData)

variable {K : Type} [Field K]

theorem transpose_phiE_mul_wOne {c : K} [Fact (Irreducible (sqPoly c))] (hc : c ≠ 0)
    (x : EAlg c) : (phiE c x)ᵀ * wMat 1 c = wMat 1 c * phiE c x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : K, x = algebraMap K (EAlg c) a +
      algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c) := ⟨_, _, eq_add_root hc x⟩
  rw [phiE_add_root]
  exact transpose_mul_wOne c a b

theorem wOne_inv_mul {c : K} (hc : c ≠ 0) : wMat 1 c⁻¹ * wMat 1 c = 1 := by
  rw [wMat, wMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [hc]

theorem uGrp_id_eq_iso {E : Type} [Field E] {n : ℕ} {w : Fin n → E} (hw : ∀ i, w i ≠ 0) :
    uGrp (RingHom.id E) (diagonal w) = CatalogueBGraphForm.isometryGroup n E (diagGL hw) := by
  ext Y
  rw [mem_uGrp, CatalogueBGraphForm.mem_isometryGroup, coe_diagGL]
  have : (Y : Matrix (Fin n) (Fin n) E).map (RingHom.id E) = Y := by
    ext
    rfl
  rw [this]

variable [Finite K]

theorem compData_orth2 (hK : ringChar K ≠ 2) {c : K} [Fact (Irreducible (sqPoly c))]
    (hc0 : c ≠ 0) {n : ℕ} (hn : 3 ≤ n) {w : Fin n → EAlg c} (hw : ∀ i, w i ≠ 0)
    {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    CompData ⁅isoCent R A, isoCent R A⁆ := by
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom)
    (σ := RingHom.id (EAlg c)) (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c)
    (wOne_inv_mul hc0) (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) (diagonal w) hR hA
  rw [hZ, uGrp_id_eq_iso hw]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, -⟩ := FiniteField.card' K
  have : CharP (EAlg c) p := charP_of_injective_algebraMap (algebraMap K (EAlg c)).injective p
  have hE : ringChar (EAlg c) ≠ 2 := by
    rw [ringChar.eq (EAlg c) p, ← ringChar.eq K p]
    exact hK
  have : Finite (EAlg c) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_EAlg hc0]
    exact pow_ne_zero 2 Nat.card_pos.ne'
  have hexc : ¬ (Nat.card (EAlg c) = 3 ∧ n ≤ 4) := by
    rintro ⟨h3, -⟩
    rw [card_EAlg hc0] at h3
    have h1 := Finite.one_lt_card (α := K)
    have : Nat.card K ^ 2 ≥ 4 := by nlinarith
    omega
  have hcd := orthComponentData hE hn (diagGL hw) (by rw [coe_diagGL]; exact diagonal_transpose _)
    hexc
  exact (show CompData ⁅CatalogueBGraphForm.isometryGroup n (EAlg c) (diagGL hw),
    CatalogueBGraphForm.isometryGroup n (EAlg c) (diagGL hw)⁆ from hcd).map
      (resGL_injective (phiE_injective c) n)

end CFSG.ComponentClassification.Burgoyne.O
