module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.Recognition.HSPinned.Native

@[expose] def vtxBinv : Array ℕ := #[
  17, 22, 0, 1, 36, 2, 44, 3, 4, 55, 5, 6, 64, 7, 8, 9, 73, 10, 76, 11, 12, 69, 13, 68, 14, 21, 15,
  16, 85, 18, 53, 19, 30, 20, 23, 87, 24, 25, 45, 26, 27, 28, 94, 29, 31, 32, 82, 33, 34, 35, 42,
  48, 37, 38, 58, 39, 89, 40, 83, 41, 43, 71, 46, 62, 47, 97, 49, 50, 51, 52, 54, 74, 56, 57, 91,
  59, 60, 61, 66, 63, 81, 65, 79, 86, 67, 75, 70, 78, 72, 96, 99, 77, 80, 90, 84, 93, 88, 92, 95,
  98]

@[expose] def vtxFun (T : Array ℕ) (i : Fin 100) : Fin 100 :=
  ⟨T[i.val]! % 100, Nat.mod_lt _ (by decide)⟩

theorem vtxFun_vtxA_vtxA : ∀ i : Fin 100, vtxFun vtxA (vtxFun vtxA i) = i := by decide +kernel

theorem vtxFun_vtxBinv_vtxB : ∀ i : Fin 100, vtxFun vtxBinv (vtxFun vtxB i) = i := by
  decide +kernel

theorem vtxFun_vtxB_vtxBinv : ∀ i : Fin 100, vtxFun vtxB (vtxFun vtxBinv i) = i := by
  decide +kernel

@[expose] def hsVa : Equiv.Perm (Fin 100) where
  toFun := vtxFun vtxA
  invFun := vtxFun vtxA
  left_inv := vtxFun_vtxA_vtxA
  right_inv := vtxFun_vtxA_vtxA

@[expose] def hsVb : Equiv.Perm (Fin 100) where
  toFun := vtxFun vtxB
  invFun := vtxFun vtxBinv
  left_inv := vtxFun_vtxBinv_vtxB
  right_inv := vtxFun_vtxB_vtxBinv

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
