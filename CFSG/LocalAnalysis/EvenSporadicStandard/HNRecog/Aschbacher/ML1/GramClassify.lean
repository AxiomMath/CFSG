module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramDefs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf Equiv Equiv.Perm


private theorem bad_00001 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 0, 0, 0, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(1, 3), (3, 4)], ofSwaps [(1, 3), (2, 4)], ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 2), (2, 1)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 2), (2, 4), (4, 3), (3, 1)], ofSwaps [(0, 3), (2, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)], ofSwaps [(0, 4), (4, 1)]],
    ![ofSwaps [(1, 3), (3, 4)], ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 2), (2, 3), (3, 4)], ofSwaps [(0, 2), (2, 1)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 2), (2, 1), (1, 3), (3, 4)], ofSwaps [(0, 3), (2, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)]],
    !![0, 0, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0], by decide +kernel⟩

private theorem bad_00010 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 0, 0, 1, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(2, 3), (3, 4)], ofSwaps [(1, 3), (3, 2)], ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 1), (1, 4)], ofSwaps [(0, 1), (1, 4), (4, 2), (2, 3)], ofSwaps [(0, 3), (3, 4), (4, 2), (2, 1)], ofSwaps [(0, 3), (1, 2)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (1, 3)]],
    ![ofSwaps [(1, 2), (2, 4)], ofSwaps [(0, 1), (1, 2)], ofSwaps [(0, 2), (2, 4), (4, 3), (3, 1)], ofSwaps [(0, 2), (2, 3), (3, 1), (1, 4)], ofSwaps [(0, 3), (3, 2), (2, 4), (4, 1)], ofSwaps [(0, 3), (1, 4)], ofSwaps [(0, 4), (4, 2), (2, 3), (3, 1)], ofSwaps [(0, 4), (4, 1), (1, 2), (2, 3)], ofSwaps [(0, 4), (1, 3)]],
    !![1, 0, 1, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 1, 1, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0], by decide +kernel⟩

private theorem bad_00100 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 0, 1, 0, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(1, 2), (3, 4)], ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 3), (3, 2)], ofSwaps [(1, 3), (2, 4)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (2, 4)], ofSwaps [(0, 3), (3, 1)], ofSwaps [(0, 3), (1, 2)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)]],
    ![ofSwaps [], ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 3), (3, 2)], ofSwaps [(1, 3), (2, 4)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (2, 3)], ofSwaps [(0, 3), (3, 1)], ofSwaps [(0, 3), (1, 2)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)]],
    !![1, 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 1, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1, 0; 1, 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 1, 1, 1; 1, 1, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 1, 1], by decide +kernel⟩

private theorem bad_00111 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 0, 1, 1, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(1, 3), (3, 4)], ofSwaps [(0, 1), (2, 3)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 2), (2, 1), (1, 3), (3, 4)], ofSwaps [(0, 2), (2, 4), (4, 1), (1, 3)], ofSwaps [(0, 3), (3, 4), (4, 2), (2, 1)], ofSwaps [(0, 3), (2, 4)], ofSwaps [(0, 3), (3, 1), (1, 2), (2, 4)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)]],
    ![ofSwaps [(1, 3), (3, 2)], ofSwaps [(1, 3), (2, 4)], ofSwaps [(0, 1), (1, 2), (2, 4), (4, 3)], ofSwaps [(0, 1), (1, 3), (3, 4), (4, 2)], ofSwaps [(0, 2), (2, 3)], ofSwaps [(0, 2), (1, 4)], ofSwaps [(0, 3), (3, 2), (2, 4), (4, 1)], ofSwaps [(0, 3), (1, 4)], ofSwaps [(0, 4), (4, 1), (1, 2), (2, 3)]],
    !![0, 1, 1, 0, 1, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 1; 1, 0, 1, 0, 0, 1, 0, 1, 1; 1, 0, 0, 1, 1, 0, 0, 1, 1; 0, 1, 0, 1, 1, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1, 1; 0, 1, 1, 0, 0, 0, 0, 1, 1], by decide +kernel⟩

private theorem bad_01000 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 0, 0, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(1, 4), (4, 2)], ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 3), (3, 4), (4, 2)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 1), (1, 4)], ofSwaps [(0, 3), (3, 4), (4, 1), (1, 2)], ofSwaps [(0, 3), (3, 1), (1, 2), (2, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)]],
    ![ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 3), (3, 4), (4, 2)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 1), (1, 4), (4, 3), (3, 2)], ofSwaps [(0, 3), (2, 4)], ofSwaps [(0, 3), (3, 4), (4, 1), (1, 2)], ofSwaps [(0, 3), (3, 1), (1, 4), (4, 2)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)], ofSwaps [(0, 4), (4, 3)]],
    !![0, 0, 0, 0, 0, 0, 1, 0, 0; 1, 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 1, 0, 0, 0, 0], by decide +kernel⟩

private theorem bad_01001 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 0, 0, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 2), (2, 3)], ofSwaps [(0, 2), (2, 4)], ofSwaps [(0, 2), (1, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)], ofSwaps [(0, 4), (4, 2)]],
    ![ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 2), (2, 4)], ofSwaps [(0, 2), (1, 4)], ofSwaps [(0, 3), (3, 1), (1, 2), (2, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)], ofSwaps [(0, 4), (4, 2)]],
    !![0, 1, 0, 1, 1, 0, 0, 1, 0; 0, 1, 1, 1, 1, 0, 1, 1, 1; 1, 0, 0, 1, 0, 1, 1, 1, 1; 0, 0, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 1, 1, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0, 0], by decide +kernel⟩

private theorem bad_01010 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 0, 1, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(2, 3), (3, 4)], ofSwaps [(1, 2), (3, 4)], ofSwaps [(1, 4), (4, 3)], ofSwaps [(0, 1), (1, 3), (3, 4), (4, 2)], ofSwaps [(0, 2), (3, 4)], ofSwaps [(0, 2), (2, 1), (1, 4), (4, 3)], ofSwaps [(0, 3), (3, 4), (4, 2), (2, 1)], ofSwaps [(0, 3), (2, 4)], ofSwaps [(0, 4), (4, 2)]],
    ![ofSwaps [(1, 3), (3, 4)], ofSwaps [(1, 3), (2, 4)], ofSwaps [(0, 1), (1, 4), (4, 3), (3, 2)], ofSwaps [(0, 1), (1, 4), (4, 2), (2, 3)], ofSwaps [(0, 2), (2, 1)], ofSwaps [(0, 2), (2, 3), (3, 4), (4, 1)], ofSwaps [(0, 3), (3, 4), (4, 1), (1, 2)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 1), (1, 3), (3, 2)]],
    !![1, 0, 0, 1, 0, 1, 1, 0, 1; 1, 0, 1, 0, 0, 1, 0, 0, 1; 1, 1, 0, 1, 1, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 1, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1, 1], by decide +kernel⟩

private theorem bad_01011 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 0, 1, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(2, 4), (4, 3)], ofSwaps [(1, 3), (3, 2)], ofSwaps [(1, 4), (2, 3)], ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 1), (2, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 1), (1, 4)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 2), (2, 1), (1, 3)]],
    ![ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 1), (1, 2), (2, 3), (3, 4)], ofSwaps [(0, 2), (2, 1)], ofSwaps [(0, 2), (2, 4), (4, 3), (3, 1)], ofSwaps [(0, 2), (2, 4), (4, 1), (1, 3)], ofSwaps [(0, 3), (1, 4)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 2), (2, 1), (1, 3)], ofSwaps [(0, 4), (1, 3)]],
    !![0, 0, 1, 1, 1, 1, 0, 1, 0; 1, 0, 1, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 1, 0, 0, 1, 1, 1; 1, 0, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 1, 1; 1, 1, 0, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 1, 0, 0], by decide +kernel⟩

private theorem bad_01100 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 1, 0, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(1, 3), (2, 4)], ofSwaps [(1, 4), (4, 2)], ofSwaps [(1, 4), (4, 3)], ofSwaps [(0, 1), (1, 2), (2, 3), (3, 4)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (1, 4)], ofSwaps [(0, 3), (3, 4)], ofSwaps [(0, 4), (4, 1)], ofSwaps [(0, 4), (4, 2)]],
    ![ofSwaps [], ofSwaps [(1, 3), (2, 4)], ofSwaps [(1, 4), (4, 2)], ofSwaps [(0, 1), (3, 4)], ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 2), (2, 4), (4, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 2), (2, 1), (1, 3)]],
    !![1, 1, 0, 1, 0, 1, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0, 1; 1, 1, 0, 0, 1, 0, 1, 1, 0; 1, 0, 0, 1, 0, 0, 0, 1, 0; 1, 0, 1, 1, 0, 1, 0, 0, 1; 1, 1, 1, 1, 1, 1, 1, 0, 1; 1, 1, 1, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 1, 1, 0, 0], by decide +kernel⟩

private theorem bad_01101 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 1, 0, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [(2, 4), (4, 3)], ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 3), (3, 4)], ofSwaps [(1, 4), (4, 3)], ofSwaps [(0, 1), (2, 4)], ofSwaps [(0, 1), (1, 4), (4, 3), (3, 2)], ofSwaps [(0, 2), (2, 4), (4, 3), (3, 1)], ofSwaps [(0, 2), (3, 4)], ofSwaps [(0, 4), (4, 1)]],
    ![ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 3), (3, 4)], ofSwaps [(1, 4), (4, 3)], ofSwaps [(0, 1), (1, 4), (4, 3), (3, 2)], ofSwaps [(0, 2), (2, 4), (4, 3), (3, 1)], ofSwaps [(0, 2), (2, 4)], ofSwaps [(0, 2), (2, 1), (1, 4), (4, 3)], ofSwaps [(0, 3), (3, 2), (2, 4), (4, 1)], ofSwaps [(0, 4), (4, 1)]],
    !![1, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 1, 1, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0, 0; 1, 0, 1, 1, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 1, 0; 1, 0, 1, 1, 0, 0, 1, 1, 0; 1, 1, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 1, 0], by decide +kernel⟩

private theorem bad_01110 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 1, 1, 0] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [], ofSwaps [(2, 3), (3, 4)], ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 4), (2, 3)], ofSwaps [(0, 1), (1, 2)], ofSwaps [(0, 1), (1, 3), (3, 4), (4, 2)], ofSwaps [(0, 1), (1, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)]],
    ![ofSwaps [], ofSwaps [(2, 3), (3, 4)], ofSwaps [(1, 2), (3, 4)], ofSwaps [(1, 2), (2, 3)], ofSwaps [(0, 1), (1, 2)], ofSwaps [(0, 1), (1, 3)], ofSwaps [(0, 1), (1, 3), (3, 2), (2, 4)], ofSwaps [(0, 2), (3, 4)], ofSwaps [(0, 3), (3, 2), (2, 1), (1, 4)]],
    !![0, 1, 0, 0, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 1, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 1, 0], by decide +kernel⟩

private theorem bad_01111 : ∃ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
    (Matrix.of fun i j => gramFn ![0, 1, 1, 1, 1] ((R i)⁻¹ * C j)) * N = 1 :=
  ⟨![ofSwaps [], ofSwaps [(1, 2), (2, 3)], ofSwaps [(0, 1), (2, 3)], ofSwaps [(0, 1), (1, 3)], ofSwaps [(0, 3), (3, 4), (4, 1), (1, 2)], ofSwaps [(0, 3), (1, 4)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 3), (3, 1), (1, 2)]],
    ![ofSwaps [], ofSwaps [(1, 2), (2, 3)], ofSwaps [(1, 4), (4, 2)], ofSwaps [(0, 1), (2, 3)], ofSwaps [(0, 3), (3, 4), (4, 1), (1, 2)], ofSwaps [(0, 3), (1, 4)], ofSwaps [(0, 4), (4, 3), (3, 2), (2, 1)], ofSwaps [(0, 4), (4, 2)], ofSwaps [(0, 4), (4, 3), (3, 1), (1, 2)]],
    !![1, 0, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 0, 0; 1, 1, 1, 1, 1, 1, 1, 1, 1; 0, 0, 1, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 0, 1], by decide +kernel⟩

private theorem pattern_cases : ∀ p : Fin 5 → ZMod 2, p 0 = 0 →
    p = ![0, 0, 0, 0, 0] ∨ p = ![0, 0, 0, 0, 1] ∨ p = ![0, 0, 0, 1, 0] ∨ p = ![0, 0, 0, 1, 1] ∨ p = ![0, 0, 1, 0, 0] ∨ p = ![0, 0, 1, 0, 1] ∨ p = ![0, 0, 1, 1, 0] ∨ p = ![0, 0, 1, 1, 1] ∨ p = ![0, 1, 0, 0, 0] ∨ p = ![0, 1, 0, 0, 1] ∨ p = ![0, 1, 0, 1, 0] ∨ p = ![0, 1, 0, 1, 1] ∨ p = ![0, 1, 1, 0, 0] ∨ p = ![0, 1, 1, 0, 1] ∨ p = ![0, 1, 1, 1, 0] ∨ p = ![0, 1, 1, 1, 1] := by
  decide +kernel

theorem gram_classify (f : A5 → ZMod 2) (hconj : ∀ x y : A5, f (y * x * y⁻¹) = f x) (h1 : f 1 = 0)
    (hne : f ≠ 0)
    (hrank : ∀ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
      (Matrix.of fun i j => f ((R i)⁻¹ * C j)) * N ≠ 1) :
    f = gramFn b₁ ∨ f = gramFn b₂ ∨ f = gramFn b₃ := by
  have hf : f = gramFn (f ∘ rep) := eq_gramFn_comp_rep f hconj
  have h0 : (f ∘ rep) 0 = 0 := by
    have : rep 0 = 1 := rfl
    simpa [Function.comp, this] using h1
  generalize f ∘ rep = p at hf h0
  subst hf
  rcases pattern_cases p h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    apply hne
    funext x
    show (![0, 0, 0, 0, 0] : Fin 5 → ZMod 2) (cls x) = 0
    generalize cls x = k
    fin_cases k <;> rfl
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_00001
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_00010
    exact hrank R C N hN
  · left; rfl
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_00100
    exact hrank R C N hN
  · right; left; rfl
  · right; right; rfl
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_00111
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01000
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01001
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01010
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01011
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01100
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01101
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01110
    exact hrank R C N hN
  · exfalso
    obtain ⟨R, C, N, hN⟩ := bad_01111
    exact hrank R C N hN

end CFSG.EvenSporadicStandard.HNRecog.ML1
