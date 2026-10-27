module

public import CFSG.LieType.Chevalley.E7Three.Product
public import CFSG.LieType.Chevalley.E7Three.Cube

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Images

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.Frames CFSG.LieType.Chevalley.E7Three.FrameWords
  CFSG.LieType.Chevalley.E7Three.Product CFSG.LieType.Chevalley.E7Three.PauliWords
  CFSG.LieType.Chevalley.E7Three.Cube CFSG.LieType.Chevalley.E7Three.Weyl

open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

theorem scalarWord_val_product (ζ : Kˣ) :
    (scalarWord ζ : ModGL .E7 K) =
      torusElt .E7 K (e7Index 1) ζ * torusElt .E7 K (e7Index 3) (ζ ^ 2) *
        torusElt .E7 K (e7Index 5) ζ * torusElt .E7 K (e7Index 6) (ζ ^ 2) := by
  have ht (i : Fin 7) : torusElt .E7 K i (1 : Kˣ) = 1 := by
    exact CFSG.Blueprint.Chevalley.torusElt_one (τ := .E7) (R := K) i
  rw [scalarWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange 7).map fun i : Fin 7 =>
    torusElt .E7 K i (ζ ^ scalarCochar i)).prod = _
  simp [List.finRange_succ, scalarCochar, ht, e7Index, mul_assoc]

theorem pairedWord_val_product (ζ : Kˣ) :
    (pairedWord ζ : ModGL .E7 K) =
      torusElt .E7 K (e7Index 0) ζ * torusElt .E7 K (e7Index 3) ζ *
        torusElt .E7 K (e7Index 6) ζ := by
  have ht (i : Fin 7) : torusElt .E7 K i (1 : Kˣ) = 1 := by
    exact CFSG.Blueprint.Chevalley.torusElt_one (τ := .E7) (R := K) i
  rw [pairedWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange 7).map fun i : Fin 7 =>
    torusElt .E7 K i (ζ ^ pairedCochar i)).prod = _
  simp [List.finRange_succ, pairedCochar, ht, e7Index, mul_assoc]

theorem theta_diagonal_zero (w : NativeFrame K) (ζ : Kˣ) :
    theta w 0 (diagonalWord ζ) = torusElt .E7 K (e7Index 3) ζ := by
  apply diagonalWord_image
  simpa [theta, nativePairs, e7ExtVec] using w.block1 0

theorem theta_diagonal_one (w : NativeFrame K) (ζ : Kˣ) :
    theta w 1 (diagonalWord ζ) = torusElt .E7 K (e7Index 6) ζ := by
  apply diagonalWord_image
  simpa [theta, nativePairs, e7ExtVec] using w.block1 1

theorem theta_diagonal_two (w : NativeFrame K) (ζ : Kˣ) :
    theta w 2 (diagonalWord ζ) = torusElt .E7 K (e7Index 0) ζ := by
  apply diagonalWord_image
  simpa [theta, nativePairs, e7ExtVec] using w.block1 2

theorem theta_central_zero (w : NativeFrame K) (ζ : Kˣ) :
    theta w 0 (centralWord ζ) =
      torusElt .E7 K (e7Index 1) ζ * torusElt .E7 K (e7Index 3) (ζ ^ 2) := by
  apply centralWord_image
  · simpa [theta, nativePairs, e7ExtVec] using w.block0 0
  · simpa [theta, nativePairs, e7ExtVec] using w.block1 0

theorem theta_central_one (w : NativeFrame K) (ζ : Kˣ) :
    theta w 1 (centralWord ζ) =
      torusElt .E7 K (e7Index 5) ζ * torusElt .E7 K (e7Index 6) (ζ ^ 2) := by
  apply centralWord_image
  · simpa [theta, nativePairs, e7ExtVec] using w.block0 1
  · simpa [theta, nativePairs, e7ExtVec] using w.block1 1

theorem prodHom_central (w : NativeFrame K) (ζ : Kˣ) :
    prodHom w ![centralWord ζ, centralWord ζ, 1] = (scalarWord ζ : ModGL .E7 K) := by
  rw [prodHom_apply]
  change theta w 0 (centralWord ζ) * theta w 1 (centralWord ζ) * theta w 2 1 = _
  rw [theta_central_zero, theta_central_one, map_one, scalarWord_val_product]
  simp only [mul_one, mul_assoc]

theorem prodHom_diagonal (w : NativeFrame K) (ζ : Kˣ) :
    prodHom w ![diagonalWord ζ, diagonalWord ζ, diagonalWord ζ] =
      (pairedWord ζ : ModGL .E7 K) := by
  rw [prodHom_apply]
  change theta w 0 (diagonalWord ζ) * theta w 1 (diagonalWord ζ) *
    theta w 2 (diagonalWord ζ) = _
  rw [theta_diagonal_zero, theta_diagonal_one, theta_diagonal_two, pairedWord_val_product]
  have hc : Commute (torusElt .E7 K (e7Index 0) ζ)
      (torusElt .E7 K (e7Index 3) ζ * torusElt .E7 K (e7Index 6) ζ) :=
    (commute_torusElt (e7Index 0) (e7Index 3) ζ ζ).mul_right
      (commute_torusElt (e7Index 0) (e7Index 6) ζ ζ)
  simpa only [mul_assoc] using hc.eq.symm

end CFSG.LieType.Chevalley.E7Three.Images
