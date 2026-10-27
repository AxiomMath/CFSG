module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlusData
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (kOmMVec kOmMEmb zThreeMat)
open CFSG.LieType.Steinberg.Sp (blockMat)

abbrev omNI : Type := Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2

abbrev omPI6 : Type := Fin 3 ⊕ Fin 3

abbrev omNI' : Type := Fin 2 ⊕ omPI6

@[expose] def omNEnc : omNI → Fin 8
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr (.inl i) => ⟨3 + i, by have := i.isLt; omega⟩
  | .inr (.inr j) => ⟨6 + j, by have := j.isLt; omega⟩

@[expose] def omPEnc6 : omPI6 → Fin 6
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr i => ⟨3 + i, by have := i.isLt; omega⟩

@[expose] def omNEnc' : omNI' → Fin 8
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr j => ⟨2 + omPEnc6 j, by have := (omPEnc6 j).isLt; omega⟩

@[expose] def omNMat (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omNI omNI (ZMod 2) :=
  Matrix.of fun i j => A (omNEnc i) (omNEnc j)

@[expose] def omNMatT (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omNI omNI' (ZMod 2) :=
  Matrix.of fun i j => A (omNEnc i) (omNEnc' j)

@[expose] def omNMatTi (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omNI' omNI (ZMod 2) :=
  Matrix.of fun i j => A (omNEnc' i) (omNEnc j)

@[expose] def omPMat6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix omPI6 omPI6 (ZMod 2) :=
  Matrix.of fun i j => A (omPEnc6 i) (omPEnc6 j)

@[expose] def omNXhTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNULTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNUSTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNX1Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNX2Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNL1Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNL2Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 1]

@[expose] def omNS1Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNS2Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNTTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 1]

@[expose] def omNTiTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 1, 0, 0, 1, 0]

@[expose] def omNHLTab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1]

@[expose] def omNHSTab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0;
    0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omNE1Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 1]

@[expose] def omNE2Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omNE3Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1]

@[expose] def omNE4Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0]

@[expose] def omNRTab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0]

@[expose] def omNXhiTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omNXh : Matrix omNI omNI (ZMod 2) := omNMat omNXhTab
@[expose] def omNXhi : Matrix omNI omNI (ZMod 2) := omNMat omNXhiTab
@[expose] def omNUL : Matrix omNI omNI (ZMod 2) := omNMat omNULTab
@[expose] def omNUS : Matrix omNI omNI (ZMod 2) := omNMat omNUSTab
@[expose] def omNX1 : Matrix omNI omNI (ZMod 2) := omNMat omNX1Tab
@[expose] def omNX2 : Matrix omNI omNI (ZMod 2) := omNMat omNX2Tab
@[expose] def omNL1 : Matrix omNI omNI (ZMod 2) := omNMat omNL1Tab
@[expose] def omNL2 : Matrix omNI omNI (ZMod 2) := omNMat omNL2Tab
@[expose] def omNS1 : Matrix omNI omNI (ZMod 2) := omNMat omNS1Tab
@[expose] def omNS2 : Matrix omNI omNI (ZMod 2) := omNMat omNS2Tab
@[expose] def omNT : Matrix omNI omNI' (ZMod 2) := omNMatT omNTTab
@[expose] def omNTi : Matrix omNI' omNI (ZMod 2) := omNMatTi omNTiTab
@[expose] def omNHL : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNHLTab
@[expose] def omNHS : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNHSTab
@[expose] def omNE1 : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNE1Tab
@[expose] def omNE2 : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNE2Tab
@[expose] def omNE3 : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNE3Tab
@[expose] def omNE4 : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNE4Tab
@[expose] def omNR : Matrix omPI6 omPI6 (ZMod 2) := omPMat6 omNRTab

theorem omNXh_mul_inv : omNXh * omNXhi = 1 := by decide +kernel
theorem omNX1_sq : omNX1 * omNX1 = 1 := by decide +kernel
theorem omNX2_sq : omNX2 * omNX2 = 1 := by decide +kernel
theorem omNL1_sq : omNL1 * omNL1 = 1 := by decide +kernel
theorem omNL2_sq : omNL2 * omNL2 = 1 := by decide +kernel
theorem omNS1_sq : omNS1 * omNS1 = 1 := by decide +kernel
theorem omNS2_sq : omNS2 * omNS2 = 1 := by decide +kernel
theorem omNUL_sq : omNUL * omNUL = 1 := by decide +kernel
theorem omNUS_sq : omNUS * omNUS = 1 := by decide +kernel
theorem omNHL_sq : omNHL * omNHL = 1 := by decide +kernel
theorem omNHS_sq : omNHS * omNHS = 1 := by decide +kernel
theorem omNE1_sq : omNE1 * omNE1 = 1 := by decide +kernel
theorem omNE2_sq : omNE2 * omNE2 = 1 := by decide +kernel
theorem omNE3_sq : omNE3 * omNE3 = 1 := by decide +kernel
theorem omNE4_sq : omNE4 * omNE4 = 1 := by decide +kernel
theorem omNR_sq : omNR * omNR = 1 := by decide +kernel

theorem omNXh_eq : omNX1 * omNX2 * omNX1 * omNX2 = omNXh := by decide +kernel
theorem omNUL_eq : omNL1 * omNL2 * omNL1 * omNL2 = omNUL := by decide +kernel
theorem omNUS_eq : omNS1 * omNS2 * omNS1 * omNS2 = omNUS := by decide +kernel
theorem omNHS_eq : omNE1 * omNE2 * omNE1 * omNE2 = omNHS := by decide +kernel
theorem omNHL_eq : omNE3 * omNE4 * omNE3 * omNE4 = omNHL := by decide +kernel

theorem omNX1_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNX1 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNX2_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNX2 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNL1_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNL1 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNL2_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNL2 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNS1_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNS1 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNS2_isom : ∀ v : omNI → ZMod 2, StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNS2 *ᵥ v) =
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := by decide +kernel
theorem omNE1_isom : ∀ v : omPI6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (omNE1 *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel
theorem omNE2_isom : ∀ v : omPI6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (omNE2 *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel
theorem omNE3_isom : ∀ v : omPI6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (omNE3 *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel
theorem omNE4_isom : ∀ v : omPI6 → ZMod 2,
    StatedQuadPlus 3 (ZMod 2) (omNE4 *ᵥ v) = StatedQuadPlus 3 (ZMod 2) v := by decide +kernel

theorem omNT_mul_Ti : omNT * omNTi = 1 := by decide +kernel
theorem omNTi_mul_T : omNTi * omNT = 1 := by decide +kernel

theorem omNT_quad : ∀ w : omNI' → ZMod 2,
    StatedQuadMinus (3 + 1) (ZMod 2) 1 1 (omNT *ᵥ w) =
      omQP (w ∘ Sum.inl) + StatedQuadPlus 3 (ZMod 2) (w ∘ Sum.inr) := by
  decide +kernel

theorem omNTi_xh_T : omNTi * omNXh * omNT = fromBlocks omXi 0 0 1 := by decide +kernel
theorem omNT_hL_Ti :
    omNT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 omNHL * omNTi = omNUL := by
  decide +kernel
theorem omNT_hS_Ti :
    omNT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 omNHS * omNTi = omNUS := by
  decide +kernel

theorem omNXh_mulVec_vec : omNXh *ᵥ kOmMVec (ZMod 2) 3 = kOmMVec (ZMod 2) 3 := by
  decide +kernel
theorem omNUL_mulVec_vec : omNUL *ᵥ kOmMVec (ZMod 2) 3 = kOmMVec (ZMod 2) 3 := by
  decide +kernel
theorem omNUS_mulVec_vec : omNUS *ᵥ kOmMVec (ZMod 2) 3 = kOmMVec (ZMod 2) 3 := by
  decide +kernel

theorem omNXh_submatrix :
    omNXh.submatrix (kOmMEmb 3) (kOmMEmb 3) = blockMat (Sum.inl 0) (Sum.inr 0) zThreeMat := by
  decide +kernel
theorem omNUL_submatrix :
    omNUL.submatrix (kOmMEmb 3) (kOmMEmb 3) = 1 + single (Sum.inl 1) (Sum.inr 1) 1 := by
  decide +kernel
theorem omNUS_submatrix : omNUS.submatrix (kOmMEmb 3) (kOmMEmb 3) =
    1 + (single (Sum.inl 1) (Sum.inr 2) 1 + single (Sum.inl 2) (Sum.inr 1) 1) := by
  decide +kernel

end CFSG.SeitzReduction.F4Pilot
