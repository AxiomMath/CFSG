module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace ProductModel

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterWeyl (weylElt weylMat weylElt_inv)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem weylMat_one_mul_uMat_mul (a b c d : K) :
    weylMat K Axis.one * uMat a b c d * weylMat K Axis.one =
      !![1, 0, b + a * d, d; a, 1, c, b; 0, 0, 1, 0; 0, 0, a, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [Finite K] [CharP K 2] in
theorem weylMat_two_mul_uMat_mul (a b c d : K) :
    weylMat K Axis.two * uMat a b c d * weylMat K Axis.two =
      !![1, b, a, c; 0, 1, 0, a; 0, d, 1, b + a * d; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [Finite K] in
theorem glMat_weylElt_mul_uElt_mul_weylElt (i : Axis) (a b c d : K) :
    glMat ((weylElt K i * uElt a b c d * weylElt K i : antiSp K) : GL (Fin 4) K) =
      weylMat K i * uMat a b c d * weylMat K i :=
  rfl

omit [Finite K] in
theorem weylElt_mul_uElt_mul_weylElt_mem_antiUnipotent_iff (i : Axis) (a b c d : K) :
    weylElt K i * uElt a b c d * weylElt K i ∈ antiUnipotent K ↔ uElt a b c d ∈ rootA K i := by
  rw [mem_antiUnipotent_iff_upper, glMat_weylElt_mul_uElt_mul_weylElt]
  cases i
  · rw [weylMat_one_mul_uMat_mul]
    have hA : uElt a b c d ∈ rootA K Axis.one ↔ a = 0 := by
      show uElt a b c d ∈ radA1 K ↔ a = 0
      constructor
      · rintro ⟨b', c', d', h⟩
        exact (uElt_inj h).1
      · rintro rfl
        exact ⟨b, c, d, rfl⟩
    rw [hA]
    constructor
    · rintro ⟨hlow, -⟩
      simpa using hlow 1 0 (by decide)
    · rintro rfl
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> simp
  · rw [weylMat_two_mul_uMat_mul]
    have hA : uElt a b c d ∈ rootA K Axis.two ↔ d = 0 := by
      show uElt a b c d ∈ radA2 K ↔ d = 0
      constructor
      · rintro ⟨a', b', c', h⟩
        exact (uElt_inj h).2.2.2
      · rintro rfl
        exact ⟨a, b, c, rfl⟩
    rw [hA]
    constructor
    · rintro ⟨hlow, -⟩
      simpa using hlow 2 1 (by decide)
    · rintro rfl
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> simp

theorem antiUnipotent_inf_map_conj_weylElt (i : Axis) :
    antiUnipotent K ⊓ (antiUnipotent K).map (MulAut.conj (weylElt K i)).toMonoidHom =
      rootA K i := by
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, weylElt_inv]
  constructor
  · rintro ⟨⟨a, b, c, d, rfl⟩, hy⟩
    exact (weylElt_mul_uElt_mul_weylElt_mem_antiUnipotent_iff i a b c d).mp hy
  · intro hy
    have hyU : y ∈ antiUnipotent K := by
      cases i
      · exact radA1_le_antiUnipotent hy
      · exact radA2_le_antiUnipotent hy
    obtain ⟨a, b, c, d, rfl⟩ := hyU
    exact ⟨⟨a, b, c, d, rfl⟩,
      (weylElt_mul_uElt_mul_weylElt_mem_antiUnipotent_iff i a b c d).mpr hy⟩

end ProductModel

end CFSG.LocalAnalysis.EvenBN.Sp4
