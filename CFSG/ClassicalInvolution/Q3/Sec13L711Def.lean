module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

structure Q8Omega {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 8
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J

end CFSG.ClassicalInvolution.Q3.Sec13
