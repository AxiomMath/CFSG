module

public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90

public section

namespace CFSG.GH74.GLS.IVK.H90

open CFSG CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem pgammaL2_conj_inr_of_pow_eq_one (x : PGammaL2 F) (hx : x ^ orderOf x.right = 1) :
    ∃ C : PGL2 F, (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
      SemidirectProduct.inr x.right :=
  GorensteinWalter.pGammaL2_conj_inr_of_pow_eq_one x hx

theorem pgammaL2_involution_conj_inr (x : PGammaL2 F) (hx : orderOf x = 2)
    (hfield : x.right ≠ 1) :
    ∃ C : PGL2 F, (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
      SemidirectProduct.inr x.right :=
  GorensteinWalter.pGammaL2_involution_conj_inr_of_finite x hx hfield

end CFSG.GH74.GLS.IVK.H90
