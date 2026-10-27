module

public import CFSG.ClassicalInvolution.Asc77.AscR10E13
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups



variable {p e : ℕ} [Fact p.Prime]

theorem ker_twistedE6Phi_sq_three (h3 : p ^ e = 3) (k : Type) [Field k]
    [Algebra (GaloisField p (2 * e)) k] :
    ∀ x ∈ (twistedE6Phi p e k).ker, x * x = 1 := by
  intro x hx
  have hp : p = 3 := (CFSG.ClassicalInvolution.Asc77.T3CII.eq_three_of_pow_eq_three h3).1
  have : CharP (GaloisField p (2 * e)) 3 := hp ▸ (inferInstance : CharP (GaloisField p (2 * e)) p)
  have hx1 : e6IsogenyFixed (frobQ p e) x = 1 := by
    apply baseChangeGL_injective (algebraMap (GaloisField p (2 * e)) k)
    rw [map_one]
    exact hx
  have hker : (x : ↥(e6Data_valid.minGroup (GaloisField p (2 * e)))) ∈
      (e6IsogenyT (GaloisField p (2 * e))).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hx1
  have hc := ker_e6IsogenyT_le_center (GaloisField p (2 * e)) hker
  have h1 := A2Isogeny.center_eq_one_e6_of_char_three (GaloisField p (2 * e)) hc
  have hx0 : x = 1 := Subtype.ext h1
  rw [hx0, mul_one]

theorem finite_twistedE6Group_three : Finite (twistedE6Group p e) := by
  have : Finite ↥(e6Data_valid.minGroup (GaloisField p (2 * e))) :=
    ChevAut.finite_minGroup e6Data_valid (GaloisField p (2 * e))
  exact Subtype.finite

end CFSG.ClassicalInvolution.ModelFacts
