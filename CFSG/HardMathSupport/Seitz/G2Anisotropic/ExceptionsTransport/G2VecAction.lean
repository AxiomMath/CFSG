module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2ModuleAction

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

section Vec

variable
  {K : Type} [Field K]

@[expose] def th (K : Type) [Field K] (γ : Fin Tag.G2.rank → ℤ) (hγ : IsQRoot γ) :
    K →+ V (Qg K) (Zg K) where
  toFun s := clsT (pinnedX .G2 K γ s)
  map_zero' := by
    show clsT (pinnedX .G2 K γ 0) = 0
    rw [pinnedX_zero .G2 K γ]
    exact clsT_Z (Zg K).one_mem
  map_add' s t := by
    show clsT (pinnedX .G2 K γ (s + t)) = clsT (pinnedX .G2 K γ s) + clsT (pinnedX .G2 K γ t)
    rw [pinnedX_add .G2 K γ s t]
    exact clsT_mul (X_mem_Qg hγ s) (X_mem_Qg hγ t)

theorem th_apply (γ : Fin Tag.G2.rank → ℤ) (hγ : IsQRoot γ) (s : K) :
    th K γ hγ s = clsT (pinnedX .G2 K γ s) := rfl

abbrev thA (K : Type) [Field K] := th K gA isQRoot_a
abbrev thU (K : Type) [Field K] := th K gU isQRoot_u
abbrev thV (K : Type) [Field K] := th K gV isQRoot_v
abbrev thB (K : Type) [Field K] := th K gB isQRoot_b

@[expose] def vec (c : K × K × K × K) : V (Qg K) (Zg K) :=
  thA K c.1 + thU K c.2.1 + thV K c.2.2.1 + thB K c.2.2.2

theorem vec_add (c d : K × K × K × K) : vec (c + d) = vec c + vec d := by
  simp only [vec, Prod.fst_add, Prod.snd_add, map_add]
  abel

@[expose] def Xmat (t : K) (c : K × K × K × K) : K × K × K × K :=
  (c.1, c.2.1 - t * c.1, c.2.2.1 + t ^ 2 * c.1 - 2 * t * c.2.1,
    c.2.2.2 + t ^ 3 * c.1 - 3 * t ^ 2 * c.2.1 + 3 * t * c.2.2.1)

@[expose] def Nmat (c : K × K × K × K) : K × K × K × K := (-c.2.2.2, -c.2.2.1, c.2.1, c.1)

theorem cx_vec (t : K) (c : K × K × K × K) : cx t (vec c) = vec (Xmat t c) := by
  have ha := cx_a t c.1
  have hu := cx_u t c.2.1
  have hv := cx_v t c.2.2.1
  have hb := cx_b t c.2.2.2
  simp only [vec, Xmat, map_add, map_sub]
  have ha' : cx t (thA K c.1) = thA K c.1 + thU K (-(t * c.1)) + thV K (t ^ 2 * c.1) +
      thB K (t ^ 3 * c.1) := ha
  have hu' : cx t (thU K c.2.1) = thU K c.2.1 + thV K (-(2 * t * c.2.1)) +
      thB K (-(3 * t ^ 2 * c.2.1)) := hu
  have hv' : cx t (thV K c.2.2.1) = thV K c.2.2.1 + thB K (3 * t * c.2.2.1) := hv
  have hb' : cx t (thB K c.2.2.2) = thB K c.2.2.2 := hb
  rw [ha', hu', hv', hb']
  simp only [map_neg]
  abel

theorem cn_vec (c : K × K × K × K) : cn (vec c) = vec (Nmat c) := by
  have ha := cn_a c.1
  have hb := cn_b c.2.2.2
  have hu := cn_u c.2.1
  have hv := cn_v c.2.2.1
  simp only [vec, Nmat, map_add, map_neg]
  have ha' : cn (thA K c.1) = thB K c.1 := ha
  have hb' : cn (thB K c.2.2.2) = thA K (-c.2.2.2) := hb
  have hu' : cn (thU K c.2.1) = thV K c.2.1 := hu
  have hv' : cn (thV K c.2.2.1) = thU K (-c.2.2.1) := hv
  rw [ha', hb', hu', hv']
  simp only [map_neg]
  abel

end Vec

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
