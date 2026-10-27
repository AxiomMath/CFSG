module
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LieType.Chevalley.CorootCoordinates

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Timmesfeld.CrossChar
variable {τ : Tag} {k : Type} [Field k]

theorem weylAct_corootCurve {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (u : kˣ) (w : WeylGroup τ) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (fun j => u ^ corootPair β (Pi.single j 1)) =
      fun j => u ^ corootPair (w • β) (Pi.single j 1) := by
  funext j
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct, CFSG.StandardType.LangRat.j4e_rootChar_corootTuple hβ]
  congr 1
  conv_rhs => rw [show Pi.single j 1 = w • (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) by
    rw [smul_inv_smul]]
  simp only [corootPair, iform_smul]

theorem commute_corootCurve_of_weyl_fixed {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (u : kˣ) (x : monomialSubgroup τ k)
    (hfix : weylQuotientHom τ k x • β = β) :
    Commute (x : ModGL τ k) (rootDiagUnit τ (fun j => u ^ corootPair β (Pi.single j 1))) := by
  have h := monomial_conj_rootDiagUnit x (fun j => u ^ corootPair β (Pi.single j 1))
  rw [weylAct_corootCurve hβ, hfix] at h
  change (x : ModGL τ k) * _ = _ * (x : ModGL τ k)
  exact (mul_inv_eq_iff_eq_mul).mp h

end CFSG.LieType.AlgebraicGroups
