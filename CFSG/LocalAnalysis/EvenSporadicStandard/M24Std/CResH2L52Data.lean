module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Unip

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH2

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def finFive : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv

@[expose] def lMatHom : Multiplicative (Matrix (Fin 2) (Fin 3) K) →* Matrix (Fin 5) (Fin 5) K :=
  (Matrix.reindexAlgEquiv ℤ K finFive : Matrix _ _ K →* Matrix _ _ K).comp blockMatHom

@[expose] def lHom : Multiplicative (Matrix (Fin 2) (Fin 3) K) →* GL (Fin 5) K :=
  MonoidHom.toHomUnits lMatHom

theorem lHom_coe (X : Multiplicative (Matrix (Fin 2) (Fin 3) K)) :
    ((lHom X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.reindex finFive finFive (Matrix.fromBlocks 1 (Multiplicative.toAdd X) 0 1) := rfl

theorem lHom_mem (X : Multiplicative (Matrix (Fin 2) (Fin 3) K)) : lHom X ∈ StatedSL 5 K := by
  apply Subgroup.subset_closure
  show ((lHom X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1
  rw [lHom_coe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem eq_one_of_scalar_lHom {c : Kˣ} {X : Multiplicative (Matrix (Fin 2) (Fin 3) K)}
    (h : Matrix.GeneralLinearGroup.scalar (Fin 5) c = lHom X) : X = 1 := by
  apply Multiplicative.toAdd.injective
  ext i j
  have h' := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)
    (finFive (Sum.inl i)) (finFive (Sum.inr j))) h
  have hne : finFive (Sum.inl i) ≠ finFive (Sum.inr j) := fun h0 =>
    Sum.inl_ne_inr (finFive.injective h0)
  simpa [lHom_coe, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hne] using h'.symm

theorem exists_hom_psl :
    ∃ ψ : Multiplicative (Matrix (Fin 2) (Fin 3) K) →* StatedProj (StatedSL 5 K),
      Function.Injective ψ :=
  exists_injective_proj (StatedSL 5 K) lHom lHom_mem fun _ _ h => eq_one_of_scalar_lHom h

end CFSG.EvenSporadicStandard.M24Std.CResH2
