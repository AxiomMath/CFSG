module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.ADG
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.B
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.CEF
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.H
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.J
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.K
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.L
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.MQRS
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.N
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.P
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.T
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.UV

public section

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_U_or_V (hD : LyonsSignedDegreeData B row f p N P)
    (hmem : B.val.map row ∈ lyonsConfigurations) :
    B.val.map row = lyonsConfiguration .U ∨ B.val.map row = lyonsConfiguration .V := by
  obtain ⟨c, hc⟩ := hmem
  cases c with
  | A1 => exact absurd hc.symm (lyons_signedDegree_ne_A1 hD)
  | A2 => exact absurd hc.symm (lyons_signedDegree_ne_A2 hD)
  | B1 => exact absurd hc.symm (lyons_signedDegree_ne_B1 hD)
  | B2 => exact absurd hc.symm (lyons_signedDegree_ne_B2 hD)
  | C1 => exact absurd hc.symm (lyons_signedDegree_ne_C1 hD)
  | C2 => exact absurd hc.symm (lyons_signedDegree_ne_C2 hD)
  | D1 => exact absurd hc.symm (lyons_signedDegree_ne_D1 hD)
  | D2 => exact absurd hc.symm (lyons_signedDegree_ne_D2 hD)
  | E1 => exact absurd hc.symm (lyons_signedDegree_ne_E1 hD)
  | E2 => exact absurd hc.symm (lyons_signedDegree_ne_E2 hD)
  | F => exact absurd hc.symm (lyons_signedDegree_ne_F hD)
  | FReflected => exact absurd hc.symm (lyons_signedDegree_ne_FReflected hD)
  | G => exact absurd hc.symm (lyons_signedDegree_ne_G hD)
  | GReflected => exact absurd hc.symm (lyons_signedDegree_ne_GReflected hD)
  | H => exact absurd hc.symm (lyons_signedDegree_ne_H hD)
  | J => exact absurd hc.symm (lyons_signedDegree_ne_J hD)
  | K => exact absurd hc.symm (lyons_signedDegree_ne_K hD)
  | L => exact absurd hc.symm (lyons_signedDegree_ne_L hD)
  | M => exact absurd hc.symm (lyons_signedDegree_ne_M hD)
  | N => exact absurd hc.symm (lyons_signedDegree_ne_N hD)
  | P => exact absurd hc.symm (lyons_signedDegree_ne_P hD)
  | Q => exact absurd hc.symm (lyons_signedDegree_ne_Q hD)
  | R => exact absurd hc.symm (lyons_signedDegree_ne_R hD)
  | S => exact absurd hc.symm (lyons_signedDegree_ne_S hD)
  | T => exact absurd hc.symm (lyons_signedDegree_ne_T hD)
  | U => exact Or.inl hc.symm
  | V => exact Or.inr hc.symm

theorem lyons_signedDegree_endpoint (hD : LyonsSignedDegreeData B row f p N P)
    (hmem : B.val.map row ∈ lyonsConfigurations) :
    P = 128 / 195 ∧ ∃ χ ∈ B, row χ = (0, 0, 1, 1, 1, 1) ∧ |f χ| = 12 ∧
      ∀ ψ ∈ B, row ψ = row χ → ψ = χ :=
  lyons_signedDegree_UV_endpoint hD (lyons_signedDegree_U_or_V hD hmem)

end CFSG.LyonsUnitaryFour
