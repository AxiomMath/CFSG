module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoAct
public import CFSG.RankThree.PartOne.KE.E7FourStabFive

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Data

@[expose] def uWord : List (Fin Tag.E8.rank) :=
  [2, 4, 3, 4, 2, 1, 3, 2, 1, 5, 4, 3, 1, 2, 6, 5, 4, 3, 1, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1,
    6, 5, 4, 7, 6, 5, 4, 3]

theorem cx_u_data : ∀ k : Fin Tag.E8.rank,
    (∑ j, (cxVec j : ℤ) * wordMat Tag.E8 uWord j k) % 5 = (czVec k : ℤ) % 5 := by
  decide +kernel

theorem wordE8Ten_row_data : ∀ k : Fin Tag.E8.rank,
    (∑ j, ((4 * czVec j : ℕ) : ℤ) * wordMat Tag.E8 TwClass.wordE8Ten j k) % 5 =
      (czVec k : ℤ) % 5 := by
  decide +kernel

theorem plane_regular_data : ∀ m : Fin 240,
    (∑ k, (czVec k : ℤ) * e8RootVec m k) % 5 = 0 →
      (∑ k, (cxVec k : ℤ) * e8RootVec m k) % 5 = 0 → False := by
  decide +kernel

end Data

section Lift

variable {L : Type} [Field L]

@[expose] def uW : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd uWord

theorem uW_smul (v : Fin Tag.E8.rank → ℤ) : uW • v = wordMat Tag.E8 uWord *ᵥ v :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 uWord v

@[expose] def nU (L : Type) [Field L] : ModGL Tag.E8 L :=
  canonicalRep (coxeterSystem Tag.E8) L uW

theorem rootChar_powVec_mulVec (u : Lˣ) (hu : IsPrimitiveRoot u 5) (c c' : Fin Tag.E8.rank → ℕ)
    (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)
    (h : ∀ k, (∑ j, (c j : ℤ) * M j k) % 5 = (c' k : ℤ) % 5) (v : Fin Tag.E8.rank → ℤ) :
    rootChar (fun k => u ^ c k) (M *ᵥ v) = rootChar (fun k => u ^ c' k) v := by
  rw [rootChar_powVec, rootChar_powVec]
  refine zpow_eq_zpow_of_modEq hu ?_
  have hsum : ∑ j, (c j : ℤ) * (M *ᵥ v) j = ∑ k, (∑ j, (c j : ℤ) * M j k) * v k := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  have hz : (((∑ k, (∑ j, (c j : ℤ) * M j k) * v k : ℤ)) : ZMod 5) =
      (((∑ k, (c' k : ℤ) * v k : ℤ)) : ZMod 5) := by
    rw [Int.cast_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_mul, Int.cast_mul]
    congr 1
    exact (ZMod.intCast_eq_intCast_iff _ _ 5).2 (h k)
  exact (ZMod.intCast_eq_intCast_iff _ _ 5).1 hz

theorem powVec_czVec (u : Lˣ) : (fun k => u ^ czVec k) = Pi.mulSingle (4 : Fin Tag.E8.rank) u := by
  funext k
  by_cases hk : k = 4
  · subst hk
    simp [czVec]
  · rw [Pi.mulSingle_eq_of_ne hk, czVec_eq_zero hk, pow_zero]

variable (L) in
theorem x_eq_conj_z {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    griessX hζ = nU L * griessZ hζ * (nU L)⁻¹ :=
  (rootDiagUnit_eq_conj_canonicalRep_iff _ _ uW).2 fun v => by
    rw [uW_smul]
    exact rootChar_powVec_mulVec _ (griessU_prim hζ) cxVec czVec _ cx_u_data v

variable (L) in
theorem nW_conj_z {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    canonicalRep (coxeterSystem Tag.E8) L
        ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten) * griessZ hζ *
      (canonicalRep (coxeterSystem Tag.E8) L
        ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten))⁻¹ = griessZ hζ ^ 4 := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff
    (fun k => griessU hζ ^ (4 * czVec k)) (fun k => griessU hζ ^ czVec k)
    ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten)).2 fun v => by
    rw [wordProd_smul_eq_wordMat_mulVec]
    exact rootChar_powVec_mulVec _ (griessU_prim hζ) (fun k => 4 * czVec k) czVec _
      wordE8Ten_row_data v
  rw [griessZ, SeitzExcOpenRest4Griess.rootDiagUnit_pow]
  rw [← h]
  congr 1
  funext k
  simp only [Pi.pow_apply, pow_mul']

end Lift

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
