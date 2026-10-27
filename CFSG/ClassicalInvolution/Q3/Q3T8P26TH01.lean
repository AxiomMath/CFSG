module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Thompson

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_boundary_of_dComp_ne (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ K₁ ∈ dComp Ω K, ∃ J₁ ∈ omegaStarNbr Ω K₁, J₁ ∉ dComp Ω K :=
  Q3T6.Mu.exists_boundary_of_dComp_ne hΩ hK hne

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Thompson
