module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (kOmegaVec kOmegaEmb zThreeMat)
open CFSG.LieType.Steinberg.Sp (blockMat)

abbrev omPI : Type := Fin (3 + 1) ⊕ Fin (3 + 1)

abbrev omMI6 : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

abbrev omPI' : Type := Fin 2 ⊕ omMI6

@[expose] def omPEnc : omPI → Fin 8
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr i => ⟨4 + i, by have := i.isLt; omega⟩

@[expose] def omMEnc6 : omMI6 → Fin 6
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr (.inl i) => ⟨2 + i, by have := i.isLt; omega⟩
  | .inr (.inr j) => ⟨4 + j, by have := j.isLt; omega⟩

@[expose] def omPEnc' : omPI' → Fin 8
  | .inl i => ⟨i, by have := i.isLt; omega⟩
  | .inr j => ⟨2 + omMEnc6 j, by have := (omMEnc6 j).isLt; omega⟩

@[expose] def omPMat (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omPI omPI (ZMod 2) :=
  Matrix.of fun i j => A (omPEnc i) (omPEnc j)

@[expose] def omPMatT (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omPI omPI' (ZMod 2) :=
  Matrix.of fun i j => A (omPEnc i) (omPEnc' j)

@[expose] def omPMatTi (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix omPI' omPI (ZMod 2) :=
  Matrix.of fun i j => A (omPEnc' i) (omPEnc j)

@[expose] def omMMat6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix omMI6 omMI6 (ZMod 2) :=
  Matrix.of fun i j => A (omMEnc6 i) (omMEnc6 j)

@[expose] def omQP {R : Type} [CommRing R] (a : Fin 2 → R) : R := a 0 * a 0 + a 0 * a 1 + a 1 * a 1

@[expose] def omPXhTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 1;
    1, 0, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 0, 0]

@[expose] def omPULTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 1, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 1]

@[expose] def omPUSTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omPR1Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omPR2Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def omPLev13Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 1]

@[expose] def omPRvTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def omPLev10Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omPSie02Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def omPTTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0]

@[expose] def omPTiTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 0, 0, 1;
    1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def omPHLTab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 1;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omPHSTab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omPE1Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 1, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1]

@[expose] def omPE2Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 1;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omPE3Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 1;
    0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def omPE4Tab : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1]

@[expose] def omPXhiTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 1, 0, 0, 0, 0]

@[expose] def omPXh : Matrix omPI omPI (ZMod 2) := omPMat omPXhTab
@[expose] def omPXhi : Matrix omPI omPI (ZMod 2) := omPMat omPXhiTab
@[expose] def omPUL : Matrix omPI omPI (ZMod 2) := omPMat omPULTab
@[expose] def omPUS : Matrix omPI omPI (ZMod 2) := omPMat omPUSTab
@[expose] def omPR1 : Matrix omPI omPI (ZMod 2) := omPMat omPR1Tab
@[expose] def omPR2 : Matrix omPI omPI (ZMod 2) := omPMat omPR2Tab
@[expose] def omPLev13 : Matrix omPI omPI (ZMod 2) := omPMat omPLev13Tab
@[expose] def omPRv : Matrix omPI omPI (ZMod 2) := omPMat omPRvTab
@[expose] def omPLev10 : Matrix omPI omPI (ZMod 2) := omPMat omPLev10Tab
@[expose] def omPSie02 : Matrix omPI omPI (ZMod 2) := omPMat omPSie02Tab
@[expose] def omPT : Matrix omPI omPI' (ZMod 2) := omPMatT omPTTab
@[expose] def omPTi : Matrix omPI' omPI (ZMod 2) := omPMatTi omPTiTab
@[expose] def omPHL : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPHLTab
@[expose] def omPHS : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPHSTab
@[expose] def omPE1 : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPE1Tab
@[expose] def omPE2 : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPE2Tab
@[expose] def omPE3 : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPE3Tab
@[expose] def omPE4 : Matrix omMI6 omMI6 (ZMod 2) := omMMat6 omPE4Tab

theorem omPXh_mul_inv : omPXh * omPXhi = 1 := by decide +kernel
theorem omPR1_sq : omPR1 * omPR1 = 1 := by decide +kernel
theorem omPR2_sq : omPR2 * omPR2 = 1 := by decide +kernel
theorem omPLev13_sq : omPLev13 * omPLev13 = 1 := by decide +kernel
theorem omPRv_sq : omPRv * omPRv = 1 := by decide +kernel
theorem omPLev10_sq : omPLev10 * omPLev10 = 1 := by decide +kernel
theorem omPSie02_sq : omPSie02 * omPSie02 = 1 := by decide +kernel
theorem omPUL_sq : omPUL * omPUL = 1 := by decide +kernel
theorem omPUS_sq : omPUS * omPUS = 1 := by decide +kernel
theorem omPHL_sq : omPHL * omPHL = 1 := by decide +kernel
theorem omPHS_sq : omPHS * omPHS = 1 := by decide +kernel
theorem omPE1_sq : omPE1 * omPE1 = 1 := by decide +kernel
theorem omPE2_sq : omPE2 * omPE2 = 1 := by decide +kernel
theorem omPE3_sq : omPE3 * omPE3 = 1 := by decide +kernel
theorem omPE4_sq : omPE4 * omPE4 = 1 := by decide +kernel

theorem omPXh_eq : omPR1 * omPR2 * omPR1 * omPR2 = omPXh := by decide +kernel
theorem omPUL_eq : omPLev13 * omPRv * omPLev13 * omPRv = omPUL := by decide +kernel
theorem omPUS_eq : omPLev10 * omPSie02 * omPLev10 * omPSie02 = omPUS := by decide +kernel
theorem omPHS_eq : omPE1 * omPE2 * omPE1 * omPE2 = omPHS := by decide +kernel
theorem omPHL_eq : omPE3 * omPE4 * omPE3 * omPE4 = omPHL := by decide +kernel

theorem omPR1_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPR1 *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPR2_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPR2 *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPLev13_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPLev13 *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPRv_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPRv *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPLev10_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPLev10 *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPSie02_isom : ∀ v : omPI → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPSie02 *ᵥ v) = StatedQuadPlus (3 + 1) (ZMod 2) v := by
  decide +kernel
theorem omPE1_isom : ∀ v : omMI6 → ZMod 2,
    StatedQuadMinus 3 (ZMod 2) 1 1 (omPE1 *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v := by
  decide +kernel
theorem omPE2_isom : ∀ v : omMI6 → ZMod 2,
    StatedQuadMinus 3 (ZMod 2) 1 1 (omPE2 *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v := by
  decide +kernel
theorem omPE3_isom : ∀ v : omMI6 → ZMod 2,
    StatedQuadMinus 3 (ZMod 2) 1 1 (omPE3 *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v := by
  decide +kernel
theorem omPE4_isom : ∀ v : omMI6 → ZMod 2,
    StatedQuadMinus 3 (ZMod 2) 1 1 (omPE4 *ᵥ v) = StatedQuadMinus 3 (ZMod 2) 1 1 v := by
  decide +kernel

theorem omPT_mul_Ti : omPT * omPTi = 1 := by decide +kernel
theorem omPTi_mul_T : omPTi * omPT = 1 := by decide +kernel

theorem omPT_quad : ∀ w : omPI' → ZMod 2,
    StatedQuadPlus (3 + 1) (ZMod 2) (omPT *ᵥ w) =
      omQP (w ∘ Sum.inl) + StatedQuadMinus 3 (ZMod 2) 1 1 (w ∘ Sum.inr) := by
  decide +kernel

theorem omPTi_xh_T : omPTi * omPXh * omPT = fromBlocks omXi 0 0 1 := by decide +kernel
theorem omPT_hL_Ti :
    omPT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 omPHL * omPTi = omPUL := by
  decide +kernel
theorem omPT_hS_Ti :
    omPT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 omPHS * omPTi = omPUS := by
  decide +kernel

theorem omPXh_mulVec_vec : omPXh *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel
theorem omPUL_mulVec_vec : omPUL *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel
theorem omPUS_mulVec_vec : omPUS *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem omPXh_submatrix :
    omPXh.submatrix (kOmegaEmb 3) (kOmegaEmb 3) = blockMat (Sum.inl 0) (Sum.inr 0) zThreeMat := by
  decide +kernel
theorem omPUL_submatrix :
    omPUL.submatrix (kOmegaEmb 3) (kOmegaEmb 3) = 1 + single (Sum.inl 1) (Sum.inr 1) 1 := by
  decide +kernel
theorem omPUS_submatrix : omPUS.submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    1 + (single (Sum.inl 1) (Sum.inr 2) 1 + single (Sum.inl 2) (Sum.inr 1) 1) := by
  decide +kernel

end CFSG.SeitzReduction.F4Pilot
