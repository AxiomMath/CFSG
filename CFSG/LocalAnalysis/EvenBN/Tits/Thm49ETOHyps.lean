module

public import Certificates.Data.Thm49ECore
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EModel

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

structure SHyp (zp : Equiv.Perm (Fin 1755)) (s : Cm → Cm) : Prop where
  mul : ∀ x ∈ GammaH, ∀ y ∈ GammaH, s (x * y) = s x * s y
  maps : ∀ x ∈ GammaH, s x ∈ GammaH
  inj : ∀ x ∈ GammaH, ∀ y ∈ GammaH, s x = s y → x = y
  tau : s tauH = tauH * inA titsZ
  z : s (inA titsZ) = inA titsZ
  R : s (tauH * inA zp) = tauH * inA zp
  M : ∀ m ∈ MH, m ∈ GammaH → s m ∈ MH

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
