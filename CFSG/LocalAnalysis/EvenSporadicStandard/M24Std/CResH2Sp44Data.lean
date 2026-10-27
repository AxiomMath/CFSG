module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Unip

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH2

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def symm2 (x : K × K × K) : Matrix (Fin 2) (Fin 2) K :=
  !![x.1, x.2.1; x.2.1, x.2.2]

theorem symm2_add (x y : K × K × K) : symm2 (x + y) = symm2 x + symm2 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm2]

omit [Field K] in
theorem symm2_transpose (x : K × K × K) : (symm2 x)ᵀ = symm2 x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm2]

theorem eq_zero_of_symm2_eq_zero {x : K × K × K} (h : symm2 x = 0) : x = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [symm2] at h00 h01 h11
  exact Prod.ext h00 (Prod.ext h01 h11)

@[expose] def symm2Hom : Multiplicative (K × K × K) →* Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
  AddMonoidHom.toMultiplicative
    { toFun := symm2
      map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [symm2]
      map_add' := symm2_add }

@[expose] def spHom : Multiplicative (K × K × K) →* GL (Fin 2 ⊕ Fin 2) K :=
  blockHom.comp symm2Hom

theorem spHom_mem (x : Multiplicative (K × K × K)) : spHom x ∈ StatedSp 2 K := by
  apply Subgroup.subset_closure
  show ((spHom x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
    Matrix.fromBlocks 0 1 (-1) 0 * ((spHom x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Matrix.fromBlocks 0 1 (-1) 0
  have h : ((spHom x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks 1 (symm2 (Multiplicative.toAdd x)) 0 1 := rfl
  rw [h, Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_multiply, symm2_transpose]

theorem exists_hom_psp :
    ∃ ψ : Multiplicative (K × K × K) →* StatedProj (StatedSp 2 K), Function.Injective ψ := by
  refine exists_injective_proj (StatedSp 2 K) spHom spHom_mem fun a c h => ?_
  have h1 := eq_one_of_scalar_blockHom (c := c) (X := symm2Hom a) h
  have h2 : symm2 (Multiplicative.toAdd a) = 0 := congrArg Multiplicative.toAdd h1
  exact Multiplicative.toAdd.injective (eq_zero_of_symm2_eq_zero h2)

end CFSG.EvenSporadicStandard.M24Std.CResH2
