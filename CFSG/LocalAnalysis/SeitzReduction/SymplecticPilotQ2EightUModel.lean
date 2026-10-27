module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignTwist
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Fischer.Classification.Basic.Heisenberg
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank
open CFSG.Fischer.Classification (CubeRel)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr mem_SU)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

namespace EightU

@[expose] def cA : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cG : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨3⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cGi : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨2⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨3⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cJ : Matrix (Fin 8) (Fin 8) F4 := antidiag 8

theorem cG_mul_cGi : cG * cGi = 1 := by decide +kernel

theorem cGi_mul_cG : cGi * cG = 1 := by decide +kernel

theorem cG_isometry : (cG.map (· ^ 2))ᵀ * cJ * cG = cJ := by decide +kernel

theorem cG_upper : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cG p.1 p.2 = 0 := by decide +kernel

theorem cG_diag : ∀ i : Fin 8, cG i i = 1 := by decide +kernel

theorem cube_cA_mul_conj :
    (cA * (cG * cA * cGi)) * (cA * (cG * cA * cGi)) * (cA * (cG * cA * cGi)) = 1 := by
  decide +kernel

theorem cube_cA_mul_conj_inv :
    (cA * (cG * (cA * cA) * cGi)) * (cA * (cG * (cA * cA) * cGi)) *
      (cA * (cG * (cA * cA) * cGi)) = 1 := by
  decide +kernel

theorem cA_mul_conj_ne : cA * (cG * cA * cGi) ≠ (cG * cA * cGi) * cA := by decide +kernel

theorem cG_planes : ∀ p : Fin 8 × Fin 8, (p.1 ∈ ({0, 1, 6, 7} : Finset (Fin 8)) ∨
    p.2 ∈ ({0, 1, 6, 7} : Finset (Fin 8))) →
      cG p.1 p.2 = (1 : Matrix (Fin 8) (Fin 8) F4) p.1 p.2 := by
  decide +kernel

theorem cA_ctuCoord : ∀ p : ((Fin 4 ⊕ Fin 4) ⊕ Fin 0) × ((Fin 4 ⊕ Fin 4) ⊕ Fin 0),
    cA (ctuCoord 4 0 p.1) (ctuCoord 4 0 p.2) =
      fromBlocks (blockMat (Sum.inl (2 : Fin 4)) (Sum.inr (2 : Fin 4)) (zThreeMat (K := F4)))
        0 0 1 p.1 p.2 := by
  decide +kernel

@[expose] def cTL : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨2⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩, ⟨1⟩]

@[expose] def cTU : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cT : Matrix (Fin 8) (Fin 8) F4 := cTL * cTU

@[expose] def cTi : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨3⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨2⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨2⟩, ⟨1⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩, ⟨1⟩]

@[expose] def cW : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩]

theorem cT_mul_cTi : cT * cTi = 1 := by decide +kernel

theorem cTi_mul_cT : cTi * cT = 1 := by decide +kernel

theorem cT_isometry : (cT.map (· ^ 2))ᵀ * cJ * cT = cJ := by decide +kernel

theorem cTi_mul_bar_cT : cTi * cT.map (· ^ 2) = cW := by decide +kernel

theorem cTL_lower : ∀ p : Fin 8 × Fin 8, p.1 < p.2 → cTL p.1 p.2 = 0 := by decide +kernel

theorem cTU_upper : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cTU p.1 p.2 = 0 := by decide +kernel

theorem cTL_diag : ∀ i : Fin 8, cTL i i = 1 := by decide +kernel

theorem cTU_diag : ∀ i : Fin 8, cTU i i = 1 := by decide +kernel

theorem cT_planes : ∀ p : Fin 8 × Fin 8, (p.1 ∈ ({2, 3, 4, 5} : Finset (Fin 8)) ∨
    p.2 ∈ ({2, 3, 4, 5} : Finset (Fin 8))) →
      cT p.1 p.2 = (1 : Matrix (Fin 8) (Fin 8) F4) p.1 p.2 := by
  decide +kernel

theorem cW_ctuCoord : ∀ p : ((Fin 4 ⊕ Fin 4) ⊕ Fin 0) × ((Fin 4 ⊕ Fin 4) ⊕ Fin 0),
    cW (ctuCoord 4 0 p.1) (ctuCoord 4 0 p.2) =
      fromBlocks (spIncl (K := F4) ((Equiv.swap (0 : Fin 4) 1 : Equiv.Perm (Fin 4)) :
        Fin 4 → Fin 4)) 0 0 1 p.1 p.2 := by
  decide +kernel

@[expose] def cA' : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩;
     ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cG' : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨2⟩, ⟨3⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

@[expose] def cGi' : Matrix (Fin 8) (Fin 8) F4 :=
  !![⟨1⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨2⟩, ⟨2⟩;
     ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩;
     ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩;
     ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩]

theorem cG'_mul_cGi' : cG' * cGi' = 1 := by decide +kernel

theorem cGi'_mul_cG' : cGi' * cG' = 1 := by decide +kernel

theorem cG'_isometry : (cG'.map (· ^ 2))ᵀ * cJ * cG' = cJ := by decide +kernel

theorem cG'_upper : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cG' p.1 p.2 = 0 := by decide +kernel

theorem cG'_diag : ∀ i : Fin 8, cG' i i = 1 := by decide +kernel

theorem cube_cA'_mul_conj :
    (cA' * (cG' * cA' * cGi')) * (cA' * (cG' * cA' * cGi')) * (cA' * (cG' * cA' * cGi')) = 1 := by
  decide +kernel

theorem cube_cA'_mul_conj_inv :
    (cA' * (cG' * (cA' * cA') * cGi')) * (cA' * (cG' * (cA' * cA') * cGi')) *
      (cA' * (cG' * (cA' * cA') * cGi')) = 1 := by
  decide +kernel

theorem cA'_mul_conj_ne : cA' * (cG' * cA' * cGi') ≠ (cG' * cA' * cGi') * cA' := by
  decide +kernel

theorem cG'_planes : ∀ p : Fin 8 × Fin 8, (p.1 ∈ ({2, 3, 4, 5} : Finset (Fin 8)) ∨
    p.2 ∈ ({2, 3, 4, 5} : Finset (Fin 8))) →
      cG' p.1 p.2 = (1 : Matrix (Fin 8) (Fin 8) F4) p.1 p.2 := by
  decide +kernel

theorem cA'_ctuCoord : ∀ p : ((Fin 4 ⊕ Fin 4) ⊕ Fin 0) × ((Fin 4 ⊕ Fin 4) ⊕ Fin 0),
    cA' (ctuCoord 4 0 p.1) (ctuCoord 4 0 p.2) =
      fromBlocks (blockMat (Sum.inl (0 : Fin 4)) (Sum.inr (0 : Fin 4)) (zThreeMat (K := F4)))
        0 0 1 p.1 p.2 := by
  decide +kernel

section Transfer

variable {F : Type} [Field F] [Finite F] [CharP F 2] (φ : F4 →+* F)

theorem unitaryInvolution_map_F4 (x : F4) : unitaryInvolution F 2 1 (φ x) = φ (x ^ 2) := by
  rw [unitaryInvolution_apply, map_pow, pow_one]

theorem conjTr_map_F4 {n : ℕ} (M : Matrix (Fin n) (Fin n) F4) :
    conjTr (unitaryInvolution F 2 1) (M.map φ) = ((M.map (· ^ 2))ᵀ).map φ := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply]
  exact unitaryInvolution_map_F4 φ (M j i)

omit [Finite F] [CharP F 2] in
theorem antidiag_map_F4 {n : ℕ} : (antidiag n : Matrix (Fin n) (Fin n) F4).map φ = antidiag n := by
  ext i j
  simp only [map_apply, antidiag, of_apply]
  split_ifs <;> simp

@[expose] noncomputable def suOfF4 {n : ℕ} (M Mi : Matrix (Fin n) (Fin n) F4) (h1 : M * Mi = 1)
    (h2 : Mi * M = 1) (hdet : M.det = 1) (hU : (M.map (· ^ 2))ᵀ * antidiag n * M = antidiag n) :
    SU (unitaryInvolution F 2 1) n :=
  ⟨⟨M.map φ, Mi.map φ, by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero φ) (map_one φ)],
      by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero φ) (map_one φ)]⟩,
    by
      change (M.map φ).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one],
    by
      change conjTr (unitaryInvolution F 2 1) (M.map φ) * antidiag n * M.map φ = antidiag n
      rw [conjTr_map_F4, ← antidiag_map_F4 φ, ← Matrix.map_mul, ← Matrix.map_mul, hU]⟩

theorem det_cG : cG.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => cG_upper (i, j) hij)]
  simp [cG_diag]

@[expose] noncomputable def gElt : SU (unitaryInvolution F 2 1) (2 * 4 + 0) :=
  suOfF4 φ cG cGi cG_mul_cGi cGi_mul_cG det_cG cG_isometry

end Transfer

section Pair

variable {F : Type} [Field F] [Finite F] [CharP F 2] (φ : F4 →+* F)
  {K : Type} [Field K] [CharP K 2] {ι : K →+* F}
  (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)

theorem coe_ctuEmbed_nsElt_two :
    (((ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (2 : Fin 4)) :
      SU (unitaryInvolution F 2 1) (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
        Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cA.map φ := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 4 0).surjective b
  rw [ctuEmbed_apply_ctuCoord, map_apply]
  rw [cA_ctuCoord (w, w')]
  rcases w with u | i
  · rcases w' with v | j
    · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, map_apply, mat_nsElt]
      simp only [blockMat, of_apply]
      split_ifs <;> simp [zThreeMat, Matrix.one_apply, apply_ite]
    · exact j.elim0
  · exact i.elim0

theorem mem_of_mem_ctuPlanes_zero_one {a : Fin (2 * 4 + 0)}
    (ha : a ∈ ctuPlanes 0 ({0, 1} : Finset (Fin 4))) : a ∈ ({0, 1, 6, 7} : Finset (Fin 8)) := by
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha
  rcases w with (q | q) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  · exact i.elim0

theorem mem_of_mem_ctuPlanes_two_three {a : Fin (2 * 4 + 0)}
    (ha : a ∈ ctuPlanes 0 ({2, 3} : Finset (Fin 4))) : a ∈ ({2, 3, 4, 5} : Finset (Fin 8)) := by
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha
  rcases w with (q | q) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  · exact i.elim0

theorem gElt_mem_ctuBlock :
    gElt φ ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4)) := by
  rw [mem_ctuBlock]
  intro a b hab
  change (cG.map φ) a b = (1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b
  rw [map_apply, cG_planes (a, b) (hab.imp mem_of_mem_ctuPlanes_zero_one
    mem_of_mem_ctuPlanes_zero_one), Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem cubeRel_conj_of_F4 {x g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    {cX cGm cGmi : Matrix (Fin 8) (Fin 8) F4}
    (hmx : (((x : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
      Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cX.map φ)
    (hmg : (((g : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
      Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cGm.map φ)
    (hmgi : (((g⁻¹ : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
      Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cGmi.map φ) (hx3 : x ^ 3 = 1)
    (h1 : (cX * (cGm * cX * cGmi)) * (cX * (cGm * cX * cGmi)) * (cX * (cGm * cX * cGmi)) = 1)
    (h2 : (cX * (cGm * (cX * cX) * cGmi)) * (cX * (cGm * (cX * cX) * cGmi)) *
      (cX * (cGm * (cX * cX) * cGmi)) = 1)
    (hne : cX * (cGm * cX * cGmi) ≠ (cGm * cX * cGmi) * cX) :
    CubeRel x (g * x * g⁻¹) ∧ x * (g * x * g⁻¹) ≠ (g * x * g⁻¹) * x := by
  have hxi : x⁻¹ = x * x := by
    rw [← pow_two]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])).symm
  have hmat : ∀ y z : SU (unitaryInvolution F 2 1) (2 * 4 + 0),
      (((y : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) =
        ((z : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F)) →
      y = z := fun y z h => Subtype.ext (Units.ext h)
  have hone : (1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) =
      (1 : Matrix (Fin 8) (Fin 8) F4).map φ := (Matrix.map_one _ (map_zero φ) (map_one φ)).symm
  refine ⟨⟨hx3, by rw [conj_pow, hx3, mul_one, mul_inv_cancel], ?_, ?_⟩, ?_⟩
  · rw [pow_three']
    apply hmat
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, hmx, hmg, hmgi]
    rw [hone, ← h1]
    simp only [Matrix.map_mul]
  · rw [pow_three', _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hxi]
    apply hmat
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, hmx, hmg, hmgi]
    rw [hone, ← h2]
    simp only [Matrix.map_mul, Matrix.mul_assoc]
  · intro h
    have h1 := congrArg (fun y : SU (unitaryInvolution F 2 1) (2 * 4 + 0) =>
      ((y : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F)) h
    simp only [Subgroup.coe_mul, Units.val_mul, hmx, hmg, hmgi] at h1
    apply hne
    apply Matrix.map_injective φ.injective
    simpa only [Matrix.map_mul] using h1

theorem cubeRel_ctuEmbed_nsElt_two :
    CubeRel (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (2 : Fin 4)))
      (gElt φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (nsElt (K := K) (2 : Fin 4)) * (gElt φ)⁻¹) ∧
    ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (2 : Fin 4)) *
        (gElt φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
          (nsElt (K := K) (2 : Fin 4)) * (gElt φ)⁻¹) ≠
      (gElt φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
          (nsElt (K := K) (2 : Fin 4)) * (gElt φ)⁻¹) *
        ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (2 : Fin 4)) :=
  cubeRel_conj_of_F4 φ (coe_ctuEmbed_nsElt_two φ hι) rfl rfl
    (by rw [← map_pow, nsElt_pow_three, map_one]) cube_cA_mul_conj cube_cA_mul_conj_inv
    cA_mul_conj_ne

omit [CharP K 2] in
theorem det_cG' : cG'.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => cG'_upper (i, j) hij)]
  simp [cG'_diag]

omit [CharP K 2] in
@[expose] noncomputable def gElt' : SU (unitaryInvolution F 2 1) (2 * 4 + 0) :=
  suOfF4 φ cG' cGi' cG'_mul_cGi' cGi'_mul_cG' det_cG' cG'_isometry

omit [CharP K 2] in
theorem gElt'_mem_ctuBlock :
    gElt' φ ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)) := by
  rw [mem_ctuBlock]
  intro a b hab
  change (cG'.map φ) a b = (1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b
  rw [map_apply, cG'_planes (a, b) (hab.imp mem_of_mem_ctuPlanes_two_three
    mem_of_mem_ctuPlanes_two_three), Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem coe_ctuEmbed_nsElt_zero :
    (((ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (0 : Fin 4)) :
      SU (unitaryInvolution F 2 1) (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
        Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cA'.map φ := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 4 0).surjective b
  rw [ctuEmbed_apply_ctuCoord, map_apply]
  rw [cA'_ctuCoord (w, w')]
  rcases w with u | i
  · rcases w' with v | j
    · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, map_apply, mat_nsElt]
      simp only [blockMat, of_apply]
      split_ifs <;> simp [zThreeMat, Matrix.one_apply, apply_ite]
    · exact j.elim0
  · exact i.elim0

theorem cubeRel_ctuEmbed_nsElt_zero :
    CubeRel (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (0 : Fin 4)))
      (gElt' φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (nsElt (K := K) (0 : Fin 4)) * (gElt' φ)⁻¹) ∧
    ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (0 : Fin 4)) *
        (gElt' φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
          (nsElt (K := K) (0 : Fin 4)) * (gElt' φ)⁻¹) ≠
      (gElt' φ * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
          (nsElt (K := K) (0 : Fin 4)) * (gElt' φ)⁻¹) *
        ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι (nsElt (K := K) (0 : Fin 4)) :=
  cubeRel_conj_of_F4 φ (coe_ctuEmbed_nsElt_zero φ hι) rfl rfl
    (by rw [← map_pow, nsElt_pow_three, map_one]) cube_cA'_mul_conj cube_cA'_mul_conj_inv
    cA'_mul_conj_ne

omit [CharP K 2] in
theorem det_cT : cT.det = 1 := by
  rw [cT, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ (fun i j hij => cTL_lower (i, j) hij),
    Matrix.det_of_isUpperTriangular (fun i j hij => cTU_upper (i, j) hij)]
  simp [cTL_diag, cTU_diag]

@[expose] noncomputable def tauElt : SU (unitaryInvolution F 2 1) (2 * 4 + 0) :=
  suOfF4 φ cT cTi cT_mul_cTi cTi_mul_cT det_cT cT_isometry

omit [CharP K 2] in
theorem tauElt_mem_ctuBlock :
    tauElt φ ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)) := by
  rw [mem_ctuBlock]
  intro a b hab
  change (cT.map φ) a b = (1 : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b
  rw [map_apply, cT_planes (a, b) (hab.imp mem_of_mem_ctuPlanes_two_three
    mem_of_mem_ctuPlanes_two_three), Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem coe_ctuEmbed_permSp_swap :
    (((ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap (0 : Fin 4) 1)) : SU (unitaryInvolution F 2 1) (2 * 4 + 0)) :
        GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) = cW.map φ := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 4 0).surjective b
  rw [ctuEmbed_apply_ctuCoord, map_apply]
  rw [cW_ctuCoord (w, w')]
  rcases w with u | i
  · rcases w' with v | j
    · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, map_apply, mat_permSp]
      rcases u with u | u <;> rcases v with v | v <;>
        simp only [spIncl, inclMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, of_apply, Matrix.zero_apply, map_zero] <;>
        split_ifs <;> simp
    · exact j.elim0
  · exact i.elim0

theorem tauElt_inv_mul_bar (hσ : ∀ c, unitaryInvolution F 2 1 (unitaryInvolution F 2 1 c) = c) :
    (tauElt φ)⁻¹ * ctuaBarAut (unitaryInvolution F 2 1) hσ (2 * 4 + 0) (tauElt φ) =
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap (0 : Fin 4) 1)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuEmbed_permSp_swap φ hι]
  change cTi.map φ * (cT.map φ).map (unitaryInvolution F 2 1) = cW.map φ
  have hb : (cT.map φ).map (unitaryInvolution F 2 1) = (cT.map (· ^ 2)).map φ := by
    ext i j
    simp only [map_apply]
    exact unitaryInvolution_map_F4 φ (cT i j)
  rw [hb, ← Matrix.map_mul, cTi_mul_bar_cT]

end Pair

end EightU

end CFSG.SeitzReduction.SymplecticPilot
