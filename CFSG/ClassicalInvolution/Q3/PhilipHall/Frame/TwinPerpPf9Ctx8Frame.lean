module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A04
public import CFSG.ClassicalInvolution.Q3.Q3T7P24Ctx8Frame

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace T7X

variable {W : Subgroup G}

@[expose] def Frame24.toQ3 (D : Asc77.T7X.Frame24 Ω W) :
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7X.Frame24 Ω W where
  c := D.c
  F := D.F
  φ := D.φ
  hφ := D.hφ
  hab := D.hab
  hcomm := D.hcomm
  hac := D.hac
  x₁ := D.x₁
  x₂ := D.x₂
  x₃ := D.x₃
  m := D.m
  hm := D.hm
  h₁ := D.h₁
  h₂ := D.h₂
  h₃ := D.h₃
  r₁ := D.r₁
  r₂ := D.r₂
  r₃ := D.r₃
  t₁ := D.t₁
  t₂ := D.t₂
  t₃ := D.t₃
  s₁ := D.s₁
  s₂ := D.s₂
  s₃ := D.s₃
  o₁ := D.o₁
  o₂ := D.o₂
  o₃ := D.o₃
  z₁ := D.z₁
  z₂ := D.z₂
  z₃ := D.z₃
  hgen := D.hgen

end T7X

namespace S24B


variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}

@[expose] def Ctx8.toFrame (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u) :
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u where
  hyp := C.hs.stand.hyp
  mem := C.hs.stand.mem
  hzK := C.hs.hz
  hK'tw := C.hs.hK'
  hne := C.hs.hne
  perp := C.hs.perp
  partI := ⟨C.hs.stand.hyp, C.hs.stand.cls, C.hs.stand.aEmpty⟩
  trans := C.hs.stand.trans
  cmSup := fun {_} hc {_} hx =>
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7K.conj_mem_sup_of C.hs.stand.hyp C.hs.stand.mem
      C.hs.hz C.hs.hK' C.hs.hne
      (CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7K.twinSet_eq_of C.hs.stand.hyp C.hs.stand.mem
        C.hs.hz C.hs.hK' C.hs.perp) hc hx
  hd := C.hd
  h8 := C.h8
  D := C.D.toQ3
  hK := C.hK
  hK' := C.hK'
  hR := C.hR
  hR' := C.hR'
  hz := C.hz

end S24B

end Asc77

end CFSG.ClassicalInvolution.Q8P
