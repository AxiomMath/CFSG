module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat CFSG.Quasithin

theorem noDelta5Norm_m22_closure :
    NoDelta5Norm ↥Mgrp :=
  noDelta5Norm_of_latSix cert cert_check m22_tle (by decide) (m := 3465) (by decide)
    (by omega) [m22AData] m22_latSix

theorem noDelta5Norm_m22
    {X : Type} [Group X] (h : IsSporadic .M22 X) : NoDelta5Norm X := by
  obtain ⟨e⟩ := h
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  exact NoDelta5Norm.of_mulEquiv
    ((MulEquiv.subgroupCongr mGens_closure).trans e'.symm) noDelta5Norm_m22_closure

end CFSG.QuasithinUnique.A5.G3
