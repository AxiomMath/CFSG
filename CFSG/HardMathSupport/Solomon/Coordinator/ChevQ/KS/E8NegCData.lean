module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux

@[expose] def r10A2pList : List (Fin Tag.E8.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, -1], ![2, 3, 4, 6, 5, 4, 3, 2],
    ![-2, -3, -4, -6, -5, -4, -3, -2], ![2, 3, 4, 6, 5, 4, 3, 1], ![-2, -3, -4, -6, -5, -4, -3, -1]]

@[expose] def r10LineWord : Fin 13 → List (Fin Tag.E8.rank)
  | 0 => ([] : List (Fin 8))
  | 1 => ([5, 6, 7, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6] : List (Fin 8))
  | 2 => ([6, 7, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6] : List (Fin 8))
  | 3 => ([6, 7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6] : List (Fin 8))
  | 4 => ([3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6] : List (Fin 8))
  | 5 => ([6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5,
      6] : List (Fin 8))
  | 6 => ([6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6] : List (Fin 8))
  | 7 => ([5, 6, 7, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6] : List (Fin 8))
  | 8 => ([6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0,
      2, 1, 3, 4, 5, 6] : List (Fin 8))
  | 9 => ([6, 7, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 6] : List (Fin 8))
  | 10 => ([5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1, 3, 4, 2,
      3, 0, 2, 1, 3, 4, 5, 6] : List (Fin 8))
  | 11 => ([6, 7, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 3, 4, 2, 3, 0,
      2, 1, 3, 4, 5, 6] : List (Fin 8))
  | 12 => ([6, 7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6] : List (Fin 8))

@[expose] def r10UWord : Fin 13 → List (Fin Tag.E8.rank)
  | 0 => ([4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 0, 2, 1] : List (Fin 8))
  | 1 => ([5, 4, 2, 0] : List (Fin 8))
  | 2 => ([4, 5, 0, 2] : List (Fin 8))
  | 3 => ([5, 4, 2, 0] : List (Fin 8))
  | 4 => ([4, 5, 0, 2] : List (Fin 8))
  | 5 => ([4, 5, 2, 0] : List (Fin 8))
  | 6 => ([5, 4, 0, 2] : List (Fin 8))
  | 7 => ([5, 4, 2, 0] : List (Fin 8))
  | 8 => ([4, 5, 0, 2] : List (Fin 8))
  | 9 => ([5, 4, 2, 0] : List (Fin 8))
  | 10 => ([5, 4, 2, 0] : List (Fin 8))
  | 11 => ([5, 4, 2, 0] : List (Fin 8))
  | 12 => ([5, 4, 2, 0] : List (Fin 8))

@[expose] def r10LineForm : Fin 13 → Fin Tag.E8.rank → ZMod 3
  | 0 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 1 => ![1, 2, 1, 0, 2, 2, 0, 0]
  | 2 => ![1, 2, 1, 0, 2, 2, 1, 0]
  | 3 => ![1, 2, 1, 0, 2, 2, 2, 0]
  | 4 => ![0, 0, 0, 1, 0, 0, 0, 0]
  | 5 => ![0, 0, 0, 1, 0, 0, 1, 0]
  | 6 => ![0, 0, 0, 1, 0, 0, 2, 0]
  | 7 => ![1, 2, 1, 1, 2, 2, 0, 0]
  | 8 => ![1, 2, 1, 1, 2, 2, 1, 0]
  | 9 => ![1, 2, 1, 1, 2, 2, 2, 0]
  | 10 => ![1, 2, 1, 2, 2, 2, 0, 0]
  | 11 => ![1, 2, 1, 2, 2, 2, 1, 0]
  | 12 => ![1, 2, 1, 2, 2, 2, 2, 0]

@[expose] def r10FormCol : Fin 13 → Fin Tag.E8.rank → ZMod 3
  | 0 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 1 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 2 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 3 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 4 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 5 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 6 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 7 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 8 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 9 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 10 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 11 => ![0, 0, 0, 0, 0, 0, 2, 0]
  | 12 => ![0, 0, 0, 0, 0, 0, 2, 0]

@[expose] def r10NegC0 (x : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  -(e8c0Word.foldr (reflect Tag.E8) x)

@[expose] def r10WAct (k : Fin 13) (x : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  (r10LineWord k).reverse.foldr (reflect Tag.E8)
    (r10NegC0 ((r10LineWord k).foldr (reflect Tag.E8) x))

theorem r10_check_E6_basis : ∀ k : Fin 13, ∀ i : Fin Tag.E8.rank, i.val < 6 →
    r10WAct k (Pi.single i 1) = (r10UWord k).foldr (reflect Tag.E8) (-(Pi.single i 1)) := by
  decide +kernel

theorem r10_check_A2p : ∀ k : Fin 13, ∀ β ∈ r10A2pList, r10WAct k β ∈ r10A2pList := by
  decide +kernel

theorem r10_check_orth : ∀ α ∈ r10A2pList, ∀ m : Fin 240, e8RootVec m 6 = 0 → e8RootVec m 7 = 0 →
    α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ e8RootVec m) = 0 := by
  decide +kernel

theorem r10_check_A2p_root : ∀ β ∈ r10A2pList, ∃ m : Fin 240, e8RootVec m = β := by
  decide +kernel

theorem r10_check_cols : ∀ k : Fin 13, ∀ i : Fin Tag.E8.rank,
    (∑ j, r10LineForm k j * ((((r10LineWord k).foldr (reflect Tag.E8) (Pi.single i 1) j : ℤ)) :
      ZMod 3)) = r10FormCol k i := by
  decide +kernel

theorem r10_check_kernel_cols : ∀ k : Fin 13, ∀ m : Fin 240,
    ((∑ i, r10FormCol k i * ((e8RootVec m i : ℤ) : ZMod 3)) = 0 ↔
      (e8RootVec m ∈ r10A2pList ∨ (e8RootVec m 6 = 0 ∧ e8RootVec m 7 = 0))) := by
  decide +kernel

theorem r10_check_A2_kill : ∀ a b c d : ZMod 3, ∀ k : Fin 13,
    (∑ i, (![a, 2 * a, a, b, 2 * a, 2 * a, c, d] : Fin Tag.E8.rank → ZMod 3) i *
      ((((r10LineWord k).foldr (reflect Tag.E8) (Pi.single 7 1) i : ℤ)) : ZMod 3)) = 0 →
    ∀ β ∈ r10A2pList, (∑ i, (![a, 2 * a, a, b, 2 * a, 2 * a, c, d] : Fin Tag.E8.rank → ZMod 3) i *
      ((((r10LineWord k).foldr (reflect Tag.E8) β i : ℤ)) : ZMod 3)) = 0 := by
  decide +kernel

@[expose] def r10C0Col : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0, 0, 0], ![-1, -2, -2, -3, -2, -1, 0, 0], ![-1, 0, -1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, -1, 0, 0],
    ![1, 1, 2, 3, 3, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem r10_check_c0cols : ∀ j : Fin Tag.E8.rank,
    e8c0Word.foldr (reflect Tag.E8) (Pi.single j 1) = r10C0Col j := by
  decide +kernel

theorem r10_form_solve : ∀ z0 z1 z2 z3 z4 z5 z6 z7 : ZMod 3,
    (-z0 - 2 * z1 - 2 * z2 - 3 * z3 - 2 * z4 - z5 = z1 ∧ z0 = z2 ∧ -z0 - z2 = z2 ∧
      z0 + z1 + z2 + z3 + z4 = z3 ∧ z4 = z5 ∧ -z4 - z5 = z5 ∧
      z0 + z1 + 2 * z2 + 3 * z3 + 3 * z4 + 2 * z5 + z6 = z6) →
    z1 = 2 * z0 ∧ z2 = z0 ∧ z4 = 2 * z0 ∧ z5 = 2 * z0 := by
  decide

theorem r10_form_cases : ∀ a b c : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0) →
    ∃ k : Fin 13, ∃ t : ZMod 3, t ≠ 0 ∧
      (![a, 2 * a, a, b, 2 * a, 2 * a, c, 0] : Fin 8 → ZMod 3) =
        fun i : Fin 8 => t * r10LineForm k i := by
  decide

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
