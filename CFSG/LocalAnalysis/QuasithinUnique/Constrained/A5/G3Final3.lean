module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporHe

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

structure Delta5Residual7 : Prop where
  j4 : J4Normalizer3
  ru : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → NoDelta5In X

theorem Delta5Residual7.toResidual6
    (h : Delta5Residual7) : Delta5Residual6 where
  j4 := h.j4
  he := fun _ _ _ _ hX => noDelta5In_he hX
  ru := h.ru

theorem a314A5Excluded_direct7
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Delta5Residual7) : A314A5Excluded :=
  a314A5Excluded_direct6 hT hcore h37 h39 hR.toResidual6

end CFSG.QuasithinUnique.A5.G3
