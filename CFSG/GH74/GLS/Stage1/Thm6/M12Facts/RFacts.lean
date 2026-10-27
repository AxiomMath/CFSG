module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Triples
public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Classes

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

@[expose] def aNF : NF := (1, 0, 0, 0)
@[expose] def bNF : NF := (0, 1, 0, 0)

@[expose] def nfComm (p q : NF) : NF := nfMul (nfMul (nfMul p q) (nfInv p)) (nfInv q)

theorem R_comm : ∀ p q : NF, pR p → pR q →
    nfMul p q = nfMul q p ∨ nfMul p q = nfMul (nfMul q p) zNF := by decide +kernel

theorem R_sq_z : ∀ p : NF, pR p → nfMul p p = zNF → pR1 p ∨ pR2 p := by decide +kernel

@[expose] def ncOK (p q : NF) : Prop :=
  nfMul p p = zNF → nfMul q q = zNF → q ≠ p → q ≠ nfMul p zNF → nfMul p q ≠ nfMul q p

instance (p q : NF) : Decidable (ncOK p q) := by unfold ncOK; infer_instance

theorem R1_noncomm : ∀ p q : NF, pR1 p → pR1 q → ncOK p q := by decide +kernel

theorem R2_noncomm : ∀ p q : NF, pR2 p → pR2 q → ncOK p q := by decide +kernel

theorem cent_card : ∀ s : NF, ¬ pR s →
    (Finset.univ.filter (fun r : NF =>
      pR r ∧ (nfMul r s = nfMul s r ∨ nfMul r s = nfMul (nfMul s r) zNF))).card = 8 := by
  decide +kernel

theorem w1_comm : nfComm yNF aNF = (3, 1, 0, 0) := by decide +kernel

theorem w2_comm : nfMul (nfComm yNF bNF) (nfInv (nfComm xNF bNF)) = (1, 1, 0, 0) := by
  decide +kernel

theorem x_not_R1 : ∀ p : NF, pR1 p → xNF ≠ p ∧ xNF ≠ nfMul p zNF := by decide +kernel
theorem x_not_R2 : ∀ p : NF, pR2 p → xNF ≠ p ∧ xNF ≠ nfMul p zNF := by decide +kernel

theorem a2_not_R1 : ∀ p : NF, pR1 p → (2, 0, 0, 0) ≠ p ∧ (2, 0, 0, 0) ≠ nfMul p zNF := by
  decide +kernel
theorem a2_not_R2 : ∀ p : NF, pR2 p → (2, 0, 0, 0) ≠ p ∧ (2, 0, 0, 0) ≠ nfMul p zNF := by
  decide +kernel

theorem pR_xNF : pR xNF := by decide +kernel
theorem pR_a2 : pR (2, 0, 0, 0) := by decide +kernel
theorem xNF_ne_zero : xNF ≠ (0, 0, 0, 0) := by decide +kernel
theorem xNF_ne_zNF : xNF ≠ zNF := by decide +kernel
theorem a2_ne_zero : ((2, 0, 0, 0) : NF) ≠ (0, 0, 0, 0) := by decide +kernel
theorem a2_ne_zNF : (2, 0, 0, 0) ≠ zNF := by decide +kernel

theorem a2_mul_z : nfMul (2, 0, 0, 0) zNF = (0, 2, 0, 0) := by decide +kernel

theorem pR1_zNF : pR1 zNF := by decide +kernel
theorem pR2_zNF : pR2 zNF := by decide +kernel
end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
