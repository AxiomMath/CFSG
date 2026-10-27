module

public import CFSG.GF2Type.Smith1979.CaseI25U43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.LieType.Multipliers.U43 (X₀ F9)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
open CFSG.GF2Type.Smith1979.Case25.U43Weights
open Matrix CFSG.Assembly.LowTwoRank

@[expose] def Ymat : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨0, 1⟩;
    ⟨2, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 0⟩;
    ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩;
    ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩]

theorem det_Ymat : Ymat.det = 1 := by decide +kernel

theorem Ymat_unitary : (Ymat.map (· ^ 3))ᵀ * Ymat = 1 := by decide +kernel

theorem Ymat_mul_rmat : Ymat * rmat 1 2 1 1 = rmat 1 0 0 0 * Ymat := by decide +kernel

theorem Ymat_not_scalar : ∀ (c : F9) (x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3),
    Ymat * rmat 0 1 0 0 ≠ c • (rmat x.1 x.2.1 x.2.2.1 x.2.2.2 * Ymat) := by decide +kernel

@[expose] noncomputable def ySU : StatedSU 4 3 F9 := toSU Ymat det_Ymat Ymat_unitary

@[expose] noncomputable def yBar : X₀ := QuotientGroup.mk ySU

theorem yBar_mul_thetaBar : yBar * thetaBar (Multiplicative.ofAdd (1, 2, 1, 1)) =
    thetaBar (Multiplicative.ofAdd (1, 0, 0, 0)) * yBar :=
  congrArg QuotientGroup.mk (ext_matrix Ymat_mul_rmat)

theorem yBar_mul_thetaBar_ne (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) :
    thetaBar x * yBar ≠ yBar * thetaBar (Multiplicative.ofAdd (0, 1, 0, 0)) := by
  intro h
  induction x using Multiplicative.rec with
  | ofAdd x =>
    obtain ⟨a, b, d, e⟩ := x
    have h' : (QuotientGroup.mk (theta4 (Multiplicative.ofAdd (a, b, d, e)) * ySU) : X₀) =
        QuotientGroup.mk (ySU * theta4 (Multiplicative.ofAdd (0, 1, 0, 0))) := h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
    obtain ⟨c, hc⟩ := h'
    have h2 : ((ySU * theta4 (Multiplicative.ofAdd (0, 1, 0, 0)) : StatedSU 4 3 F9) :
        GL (Fin 4) F9) = ((theta4 (Multiplicative.ofAdd (a, b, d, e)) * ySU : StatedSU 4 3 F9) :
        GL (Fin 4) F9) * Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
      rw [hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h3 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9)) h2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
    have e1 : ((((ySU * theta4 (Multiplicative.ofAdd (0, 1, 0, 0)) : StatedSU 4 3 F9) :
        GL (Fin 4) F9)) : Matrix (Fin 4) (Fin 4) F9) = Ymat * rmat 0 1 0 0 := rfl
    have e2 : ((((theta4 (Multiplicative.ofAdd (a, b, d, e)) * ySU : StatedSU 4 3 F9) :
        GL (Fin 4) F9)) : Matrix (Fin 4) (Fin 4) F9) = rmat a b d e * Ymat := rfl
    rw [e1, e2] at h3
    refine Ymat_not_scalar (c : F9) (a, b, d, e) ?_
    rw [h3]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]

end CFSG.GF2Type.Smith1979.IdxFour
