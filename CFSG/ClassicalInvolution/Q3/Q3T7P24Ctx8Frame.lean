module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A04
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngC

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)

namespace S24B

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure Ctx8Frame (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  hyp : HypOmegaGen Ω
  mem : K ∈ Ω
  hzK : IsUniqueInvolution K z
  hK'tw : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = {K, K'}
  partI : Q3CL.PartIHypG Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  cmSup : ∀ {c : G}, c ∈ Subgroup.centralizer ({z} : Set G) →
    ∀ {x : G}, x ∈ K ⊔ K' → c * x * c⁻¹ ∈ K ⊔ K'
  hd : Hyp24Data Ω K K' W S R R' z u
  h8 : Nat.card ↥R = 8
  D : T7X.Frame24 Ω W
  hK : D.F.ρ.K = K
  hK' : D.F.ρ'.K = K'
  hR : D.F.ρ.R = R
  hR' : D.F.ρ'.R = R'
  hz : D.F.z = z

namespace Ctx8Frame

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem twinSet_eq : twinSet Ω K = {K, K'} :=
  T7K.twinSet_eq_of C.hyp C.mem C.hzK C.hK'tw C.perp

end Ctx8Frame


variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}

@[expose] def Ctx8.toFrame (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u) :
    Ctx8Frame Ω K K' W S R R' z u where
  hyp := C.hs.stand.hyp
  mem := C.hs.stand.mem
  hzK := C.hs.hz
  hK'tw := C.hs.hK'
  hne := C.hs.hne
  perp := C.hs.perp
  partI := ⟨C.hs.stand.hyp, C.hs.stand.cls, C.hs.stand.aEmpty⟩
  trans := C.hs.stand.trans
  cmSup := fun {_} hc {_} hx =>
    T7K.conj_mem_sup_of C.hs.stand.hyp C.hs.stand.mem C.hs.hz C.hs.hK' C.hs.hne
      (T7K.twinSet_eq_of C.hs.stand.hyp C.hs.stand.mem C.hs.hz C.hs.hK' C.hs.perp) hc hx
  hd := C.hd
  h8 := C.h8
  D := C.D
  hK := C.hK
  hK' := C.hK'
  hR := C.hR
  hR' := C.hR'
  hz := C.hz

end S24B

end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
