module

public import CFSG.RankThree.PartOne.KE8F.E8Lat
public import Certificates.Data.E8FiveStab

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE8F Matrix

@[expose] def cWord : List (Fin Tag.E8.rank) :=
  [5, 6, 7, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 0, 3, 1, 2, 3, 4, 5, 6, 7, 5, 6, 4, 5, 2,
    3, 4, 1, 3, 2, 0, 3, 1, 2, 3, 5, 4, 6, 5, 2, 3, 1, 4, 3, 4]

theorem wordMat_cWord_pow_five : wordMat Tag.E8 cWord ^ 5 = 1 := by decide +kernel

theorem wordMat_cWord_comm :
    wordMat Tag.E8 cWord * wordMat Tag.E8 e8P4WW =
      wordMat Tag.E8 e8P4WW * wordMat Tag.E8 cWord := by
  decide +kernel

theorem wordMat_cWord_ne_one : wordMat Tag.E8 cWord ≠ 1 := by decide +kernel

@[expose] def cTrans : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  ((wordMat Tag.E8 cWord).map (Int.cast : ℤ → ZMod 5))ᵀ

@[expose] def eigTwo (a : Fin 4 → ZMod 5) : Fin 8 → ZMod 5 := fun i => e8FiveEig2 a i

@[expose] def eigThree (a : Fin 4 → ZMod 5) : Fin 8 → ZMod 5 := fun i => e8FiveEig3 a i

theorem fixed_ncard_two :
    Set.ncard {a : Fin 4 → ZMod 5 | cTrans *ᵥ eigTwo a = eigTwo a} ≤ 5 := by
  have h : {a : Fin 4 → ZMod 5 | cTrans *ᵥ eigTwo a = eigTwo a} =
      ↑(Finset.univ.filter fun a : Fin 4 → ZMod 5 => cTrans *ᵥ eigTwo a = eigTwo a) := by
    ext a
    simp
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem fixed_ncard_three :
    Set.ncard {a : Fin 4 → ZMod 5 | cTrans *ᵥ eigThree a = eigThree a} ≤ 5 := by
  have h : {a : Fin 4 → ZMod 5 | cTrans *ᵥ eigThree a = eigThree a} =
      ↑(Finset.univ.filter fun a : Fin 4 → ZMod 5 => cTrans *ᵥ eigThree a = eigThree a) := by
    ext a
    simp
  rw [h, Set.ncard_coe_finset]
  decide +kernel

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
