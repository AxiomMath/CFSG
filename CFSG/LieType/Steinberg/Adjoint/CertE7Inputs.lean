module

public import CFSG.LieType.Steinberg.Adjoint.CertE7Weyl
public import CFSG.LieType.Steinberg.Adjoint.CertE7Pairs
public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import CFSG.LieType.Steinberg.Adjoint.CertPinned
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate121

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

theorem noG2_E7 : NoG2 .E7 := fun i => Or.inl (by simp [Tag.symmetrizer])

end CFSG.LieType.Steinberg.Adjoint
