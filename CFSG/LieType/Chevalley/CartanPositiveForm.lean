module

public import CFSG.LieType.Chevalley.WeylSpace
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix

@[expose] def leadingMinors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : List ℤ :=
  (List.finRange n).map fun k : Fin n =>
    (M.submatrix (Fin.castLE k.isLt) (Fin.castLE k.isLt) :
      Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) ℤ).det

theorem leadingMinors_eq_laplace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    leadingMinors M = (List.finRange n).map fun k : Fin n =>
      laplaceDet ((k : ℕ) + 1) (M.submatrix (Fin.castLE k.isLt) (Fin.castLE k.isLt)) := by
  unfold leadingMinors
  refine List.map_congr_left fun k _ => ?_
  rw [laplaceDet_eq_det]

theorem symmetrizedCartan_isSymm (τ : Tag) : τ.symmetrizedCartan.IsSymm := by
  cases τ <;> decide +kernel

theorem cartan_positive_form :
    (∀ τ : Tag, τ.symmetrizedCartan.IsSymm ∧
      (τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)).PosDef) ∧
    leadingMinors Tag.G2.symmetrizedCartan = [6, 3] ∧
    leadingMinors Tag.F4.symmetrizedCartan = [4, 12, 8, 4] ∧
    leadingMinors Tag.D4.symmetrizedCartan = [2, 4, 4, 4] ∧
    leadingMinors Tag.E6.symmetrizedCartan = [2, 4, 6, 5, 4, 3] ∧
    leadingMinors Tag.E7.symmetrizedCartan = [2, 4, 6, 5, 4, 3, 2] ∧
    leadingMinors Tag.E8.symmetrizedCartan = [2, 4, 6, 5, 4, 3, 2, 1] := by
  refine ⟨fun τ => ⟨symmetrizedCartan_isSymm τ, posDef_symmetrizedCartan τ⟩, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> rw [leadingMinors_eq_laplace] <;> decide +kernel

end CFSG.LieType.Chevalley
