module

public import CFSG.GF2Type.Smith1979.IdxFourModelStab
public import Certificates.Certificate17641
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module CFSG.GF2Type.Smith1979.GammaU

theorem sub6_E0
    {U : Submodule (ZMod 2) V12} (hdim : finrank (ZMod 2) U = 6)
    (hinv : ∀ s ∈ stabIn E0 a0V, ∀ u ∈ U, s u ∈ U) : ∃ w ∈ U, inO378 w := by
  have hcard : Nat.card U = 64 := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 U, hdim]
    norm_num
  exact Certificates.certificate17641 U
    (fun s hs hfix => hinv s (mem_stabIn.2 ⟨hs, hfix⟩)) (by omega)

end CFSG.GF2Type.Smith1979.IdxFour
