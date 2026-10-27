module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module
open scoped Matrix

abbrev stdMat (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks 0 1 (-1) 0

noncomputable def stdForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  Matrix.toBilin' (stdMat n)

theorem zmod2_add_self_eq_zero (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem zmod2_neg_eq (x : ZMod 2) : -x = x := by
  revert x
  decide

theorem stdMat_mulVec_inl (n : ℕ) (w : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    (stdMat n *ᵥ w) (Sum.inl i) = w (Sum.inr i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, stdMat, Matrix.fromBlocks_apply₁₂,
    Matrix.one_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem stdMat_mulVec_inr (n : ℕ) (w : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    (stdMat n *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, stdMat, Matrix.fromBlocks_apply₂₁,
    Matrix.neg_apply, Matrix.one_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb, zmod2_neg_eq]) (by simp)]
  simp [neg_one_mul, zmod2_neg_eq]

theorem stdForm_apply (n : ℕ) (v w : Fin n ⊕ Fin n → ZMod 2) :
    stdForm n v w = ∑ i : Fin n, (v (Sum.inl i) * w (Sum.inr i) + v (Sum.inr i) * w (Sum.inl i)) := by
  rw [stdForm, Matrix.toBilin'_apply', dotProduct, Fintype.sum_sum_type,
    Finset.sum_add_distrib]
  simp only [stdMat_mulVec_inl, stdMat_mulVec_inr]

theorem stdForm_isAlt (n : ℕ) : (stdForm n).IsAlt := by
  intro v
  rw [stdForm_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [mul_comm (v (Sum.inr i)) (v (Sum.inl i))]
  exact zmod2_add_self_eq_zero _

theorem stdForm_symm (n : ℕ) (v w : Fin n ⊕ Fin n → ZMod 2) :
    stdForm n v w = stdForm n w v := by
  rw [stdForm_apply, stdForm_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem stdForm_sepLeft (n : ℕ) (v : Fin n ⊕ Fin n → ZMod 2)
    (hv : ∀ w, stdForm n v w = 0) : v = 0 := by
  have hinl : ∀ i, v (Sum.inl i) = 0 := by
    intro i
    have h := hv (Pi.single (Sum.inr i) 1)
    rw [stdForm_apply] at h
    simpa [Pi.single_apply] using h
  have hinr : ∀ i, v (Sum.inr i) = 0 := by
    intro i
    have h := hv (Pi.single (Sum.inl i) 1)
    rw [stdForm_apply] at h
    simpa [Pi.single_apply] using h
  funext x
  rcases x with i | i
  · exact hinl i
  · exact hinr i

theorem stdForm_nondeg (n : ℕ) : (stdForm n).Nondegenerate :=
  ⟨fun v hv => stdForm_sepLeft n v hv,
    fun w hw => stdForm_sepLeft n w (fun v => by rw [stdForm_symm]; exact hw v)⟩

theorem stdForm_finrank (n : ℕ) :
    Module.finrank (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem exists_stdIso (n : ℕ) :
    Nonempty (StatedSp n (ZMod 2) ≃* TauCeti.BilinForm.isometryGroup (stdForm n)) := by
  let inst : @Module (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) _ AddCommGroup.toAddCommMonoid :=
    Pi.module _ _ _
  have hfd : FiniteDimensional (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) := Module.Finite.pi
  obtain ⟨m, hm, ⟨φ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_bilinIsometryGroup_equiv_statedSp
      (K := ZMod 2) (V := Fin n ⊕ Fin n → ZMod 2) (f := stdForm n)
      (stdForm_nondeg n) (stdForm_isAlt n)
  have hmn : m = n := by
    have h1 := stdForm_finrank n
    have h2 : Module.finrank (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) = 2 * m := hm
    omega
  subst hmn
  exact ⟨φ.symm.trans (CFSG.HardMathSupport.Solomon.Coordinator.mclt_bilinIsometryGroupEquiv
    (stdForm m))⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
