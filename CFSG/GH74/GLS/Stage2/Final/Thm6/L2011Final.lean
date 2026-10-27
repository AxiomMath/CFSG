module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011SylowIn
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011YStep
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentAPf
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011B9bMain
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentCore
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S5

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6
open CFSG.GH74.GLS.Stage2.Local.P34 (GHSchreier)

theorem centCoreProp_proved : CentCoreProp :=
  fun _ _ _ _ _ _ hJH hJle hperf hF₁H hF₁N hcop _ hS₀J hS₀F =>
    l2011_cent_core hJH hJle hperf hF₁H hF₁N hcop hS₀J hS₀F

theorem lemma20_11_of_leaves (hAd : Adapter20_9) (hCF : CFTypeAut) (hSch : GHSchreier)
    (h31a : IVK.IVK_3_1a) (h31c : IVK.IVK_3_1c) (h31g : IVK.Proofs2.IVK_3_1g_fixed) :
    Lemma20_11 := by
  have h20b : Coprime20b := coprime20b hSch
  have hcore : CentCoreProp := centCoreProp_proved
  exact lemma20_11_of_parts
    (pkg2010_of_parts hAd (sylowIn20_of hCF h20b hcore) (centS20_of h20b hcore)
      (yStep20_of hCF h20b hcore) (centA20_of hCF h20b hcore))
    (l2011S5 h31a h31c h31g)

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
