module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporM24

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

structure Delta5Residual6 : Prop where
  j4 : J4Normalizer3
  he : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .He X → NoDelta5In X
  ru : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → NoDelta5In X

theorem Delta5Residual6.toResidual5
    (h : Delta5Residual6) : Delta5Residual5 where
  j4 := h.j4
  m24 := fun _ _ _ _ hX => noDelta5In_m24 hX
  he := h.he
  ru := h.ru

theorem a314A5Excluded_direct6
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Delta5Residual6) : A314A5Excluded :=
  a314A5Excluded_direct5 hT hcore h37 h39 hR.toResidual5

end CFSG.QuasithinUnique.A5.G3
