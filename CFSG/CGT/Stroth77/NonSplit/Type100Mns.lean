module

public import Certificates.Certificate778704

public section

namespace CFSG.CGT.Stroth77


theorem toA_add : ∀ x y : Torus (Type100.k 1), toA (x + y) = toA x * toA y :=
  Certificates.certificate778704.1

theorem toA_injective : Function.Injective toA := fun x y h =>
  Certificates.certificate778704.2.1 x y h

theorem toA_mem : ∀ x : Torus (Type100.k 1), toA x ∈ bfsList gensA 60 :=
  Certificates.certificate778704.2.2.1

theorem toA_uv : ∀ x : Torus (Type100.k 1),
    toA ((Type100.action 1).φuv x) = mnsUV⁻¹ * toA x * mnsUV :=
  Certificates.certificate778704.2.2.2.1

theorem toA_t : ∀ x : Torus (Type100.k 1),
    toA ((Type100.action 1).φt x) = mnsT⁻¹ * toA x * mnsT :=
  Certificates.certificate778704.2.2.2.2.1

theorem toA_u : ∀ x : Torus (Type100.k 1),
    toA ((Type100.action 1).φu x) = mnsU⁻¹ * toA x * mnsU :=
  Certificates.certificate778704.2.2.2.2.2.1

theorem toA_rho : ∀ x : Torus (Type100.k 1),
    toA ((Type100.action 1).φρ x) = mnsRho⁻¹ * toA x * mnsRho :=
  Certificates.certificate778704.2.2.2.2.2.2

end CFSG.CGT.Stroth77
