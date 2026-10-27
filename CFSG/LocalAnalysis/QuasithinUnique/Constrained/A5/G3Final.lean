module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3D4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3F4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Tits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporHS

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank

theorem rank2NoDelta5
    : Rank2NoDelta5 :=
  rank2NoDelta5_of_parts
    { l3 := fun _ _ _ L P f hf hL hP => not_isDelta5_perfectCore_l3 L P f hf hL hP
      sp4 := fun _ _ _ L P f hf hL hP => not_isDelta5_perfectCore_sp4 L P f hf hL hP
      g2 := fun _ _ _ L P f hf hL hP => not_isDelta5_perfectCore_g2 L P f hf hL hP
      d4 := fun _ _ _ L P f hf hL hP => not_isDelta5_perfectCore_d4 L P f hf hL hP
      f4 := fun _ _ _ L P f hodd hf hL hP => not_isDelta5_perfectCore_f4 L P f hodd hf hL hP
      tits := fun _ _ _ L P hL hP => not_isDelta5_perfectCore_tits L P hL hP }

structure Delta5Residual5 : Prop where
  j4 : J4Normalizer3
  m24 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M24 X → NoDelta5In X
  he : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .He X → NoDelta5In X
  ru : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → NoDelta5In X

theorem Delta5Residual5.toResidual3
    (h : Delta5Residual5) : Delta5Residual3 where
  rows := ⟨rank2NoDelta5, mathieuNoDelta5, a314J4NoDelta5_of_normalizer h.j4⟩
  m24 := h.m24
  hs := fun _ _ _ _ hX => noDelta5In_hs hX
  he := h.he
  ru := h.ru

theorem a314A5Excluded_direct5
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Delta5Residual5) : A314A5Excluded :=
  a314A5Excluded_direct3 hT hcore h37 h39 hR.toResidual3

end CFSG.QuasithinUnique.A5.G3
