
module

public import CFSG.GH74.E2.Alpha1CoreBase

public import CFSG.GH74.E2.Alpha1Rank
public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.DirectProd
public import CFSG.GH74.E2.Tools
public import CFSG.GH74.E2.DirectSylow
public import CFSG.GH74.E2.Alpha1AutCert
public import CFSG.GH74.GLS.Types
public import CFSG.Open.Catalog
public import CFSG.GH74.E2.NonCentralProd
public import CFSG.GH74.E2.QuasiRank
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.CaseIGlue
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1CoreInputs
public meta import CFSG.GH74.E2.Alpha1CoreInputs
public import Certificates.Certificate5005

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral

section SD16Facts

theorem sd16_central_involutions_aux :
    ∀ x y z : SD16M, IsCentralInv16 x → IsCentralInv16 y →
    IsCentralInv16 z → x = y ∨ x = z ∨ y = z :=
  Certificates.certificate5005.2

theorem sd16_central_involutions :
    ∀ x y z : SD16M, (∀ w, w * x = x * w) → x * x = 1 →
    (∀ w, w * y = y * w) → y * y = 1 → (∀ w, w * z = z * w) → z * z = 1 →
    x = y ∨ x = z ∨ y = z :=
  fun x y z hx hx2 hy hy2 hz hz2 =>
    sd16_central_involutions_aux x y z ⟨hx, hx2⟩ ⟨hy, hy2⟩ ⟨hz, hz2⟩

end SD16Facts

end CFSG.GH74.E2
