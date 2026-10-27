module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase
import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterWeyl
  (swapSL upperSL coe_upperSL weylElt sHom_swapSL sHom_upperSL_mem)

variable {K : Type} [Field K]

variable (K) in
@[expose] def weylSL2 [CharP K 2] : SL₂ K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem coe_weylSL2 [CharP K 2] :
    ((weylSL2 K : SL₂ K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem weylSL2_eq_swapSL [CharP K 2] : weylSL2 K = swapSL :=
  rfl

theorem weylSL2_mul_self [CharP K 2] : weylSL2 K * weylSL2 K = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_weylSL2, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL2_inv [CharP K 2] : (weylSL2 K)⁻¹ = weylSL2 K :=
  inv_eq_of_mul_eq_one_right weylSL2_mul_self

theorem upperSL_mul (x y : K) : upperSL x * upperSL y = upperSL (x + y) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL, coe_upperSL, coe_upperSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperSL_zero : upperSL (0 : K) = 1 := by
  ext i j
  rw [coe_upperSL, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem upperSL_neg (x : K) : (upperSL x)⁻¹ = upperSL (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [upperSL_mul, add_neg_cancel, upperSL_zero])

theorem upperSL_injective : Function.Injective (upperSL : K → SL₂ K) := by
  intro x y h
  simpa [coe_upperSL] using congrArg (fun g : SL₂ K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h

variable (K) in
@[expose] def upperSL2 : Subgroup (SL₂ K) where
  carrier := Set.range upperSL
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (upperSL_mul x y).symm⟩
  one_mem' := ⟨0, upperSL_zero⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, (upperSL_neg x).symm⟩

theorem upperSL_mem_upperSL2 (x : K) : upperSL x ∈ upperSL2 K :=
  ⟨x, rfl⟩

theorem mem_upperSL2_iff {g : SL₂ K} : g ∈ upperSL2 K ↔ ∃ x : K, upperSL x = g :=
  Iff.rfl

theorem card_upperSL2 : Nat.card (upperSL2 K) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : K => (⟨upperSL x, upperSL_mem_upperSL2 x⟩ : upperSL2 K)) ⟨?_, ?_⟩)).symm
  · exact fun x y h => upperSL_injective (congrArg Subtype.val h)
  · rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩

theorem coe_weylSL2_mul_upperSL_mul_inv [CharP K 2] (x : K) :
    ((weylSL2 K * upperSL x * (weylSL2 K)⁻¹ : SL₂ K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; x, 1] := by
  rw [weylSL2_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_weylSL2, coe_upperSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sHom_weylSL2 [CharP K 2] [Finite K] (i : Axis) : sHom K i (weylSL2 K) = weylElt K i := by
  rw [weylSL2_eq_swapSL]
  exact sHom_swapSL i

theorem sHom_upper_le_antiUnipotent [CharP K 2] [Finite K] (i : Axis) :
    (upperSL2 K).map (sHom K i) ≤ antiUnipotent K := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact sHom_upperSL_mem i x

theorem upperSL2_sup_conj_weyl [CharP K 2] :
    upperSL2 K ⊔ (upperSL2 K).map (MulAut.conj (weylSL2 K)).toMonoidHom = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
    Subgroup.closure_le]
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact Subgroup.mem_sup_left (upperSL_mem_upperSL2 x)
  · exact Subgroup.mem_sup_right ⟨upperSL x, upperSL_mem_upperSL2 x,
      Subtype.ext (coe_weylSL2_mul_upperSL_mul_inv x)⟩

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
