module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UAut
public import Certificates.Data.U43SigmaFix
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.E4QuatCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem matR0_mul : matN9 codeR0 * matN9 codeR0 = 1 := by decide +kernel

theorem matU0_mul : matN9 codeU0 * matN9 205898105840601 = 1 := by decide +kernel

theorem matU0_mul' : matN9 205898105840601 * matN9 codeU0 = 1 := by decide +kernel

theorem matV0_mul : matN9 codeV0 * matN9 68818663899687 = 1 := by decide +kernel

theorem matV0_mul' : matN9 68818663899687 * matN9 codeV0 = 1 := by decide +kernel

theorem matU1_mul : matN9 codeU1 * matN9 617683856696201 = 1 := by decide +kernel

theorem matU1_mul' : matN9 617683856696201 * matN9 codeU1 = 1 := by decide +kernel

theorem matV1_mul : matN9 codeV1 * matN9 617683856656887 = 1 := by decide +kernel

theorem matV1_mul' : matN9 617683856656887 * matN9 codeV1 = 1 := by decide +kernel

@[expose] def matR0 : GL (Fin 4) F9 := ⟨matN9 codeR0, matN9 codeR0, matR0_mul, matR0_mul⟩

@[expose] def matU0 : GL (Fin 4) F9 :=
  ⟨matN9 codeU0, matN9 205898105840601, matU0_mul, matU0_mul'⟩

@[expose] def matV0 : GL (Fin 4) F9 := ⟨matN9 codeV0, matN9 68818663899687, matV0_mul, matV0_mul'⟩

@[expose] def matU1 : GL (Fin 4) F9 :=
  ⟨matN9 codeU1, matN9 617683856696201, matU1_mul, matU1_mul'⟩

@[expose] def matV1 : GL (Fin 4) F9 :=
  ⟨matN9 codeV1, matN9 617683856656887, matV1_mul, matV1_mul'⟩

@[expose] noncomputable def glN9 (k : ℕ) : GL (Fin 4) F9 := by
  classical
  exact if h : IsUnit (matN9 k).det then Matrix.GeneralLinearGroup.mk'' (matN9 k) h else 1

theorem glN9_val {k : ℕ} (h : (matN9 k).det ≠ 0) :
    (glN9 k : Matrix (Fin 4) (Fin 4) F9) = matN9 k := by
  rw [glN9, dif_pos (isUnit_iff_ne_zero.mpr h)]
  rfl

@[expose] noncomputable def r0P : Equiv.Perm (Fin 820) := perm820 matR0

@[expose] noncomputable def u0P : Equiv.Perm (Fin 820) := perm820 matU0

@[expose] noncomputable def v0P : Equiv.Perm (Fin 820) := perm820 matV0

@[expose] noncomputable def u1P : Equiv.Perm (Fin 820) := perm820 matU1

@[expose] noncomputable def v1P : Equiv.Perm (Fin 820) := perm820 matV1

@[expose] noncomputable def d2P : Equiv.Perm (Fin 820) := perm820 dM1

@[expose] noncomputable def s01P : Equiv.Perm (Fin 820) := perm820 (glN9 codeS01)

@[expose] noncomputable def w0P : Equiv.Perm (Fin 820) := perm820 (glN9 codeW0)

@[expose] noncomputable def y0P : Equiv.Perm (Fin 820) := perm820 (glN9 codeY0)

@[expose] noncomputable def gamP : List (Equiv.Perm (Fin 820)) :=
  gamCodes.map fun k => perm820 (glN9 k)

@[expose] noncomputable def K0 : Subgroup (Equiv.Perm (Fin 820)) := Subgroup.closure {u0P, v0P}

@[expose] noncomputable def K1 : Subgroup (Equiv.Perm (Fin 820)) := Subgroup.closure {u1P, v1P}

@[expose] noncomputable def L0P : List (Equiv.Perm (Fin 820)) := q8Elems r0P u0P v0P

@[expose] noncomputable def L1P : List (Equiv.Perm (Fin 820)) := q8Elems r0P u1P v1P

@[expose] def CfgCore (y : Equiv.Perm (Fin 820)) : Prop :=
  y * u0P = u0P * y ∧ y * v0P = v0P * y ∧ y * y = 1 ∧
    ∃ x ∈ L1P.drop 2, y * u1P = x * u1P * x⁻¹ * y ∧ y * v1P = x * v1P * x⁻¹ * y

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
