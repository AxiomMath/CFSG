module

public import CFSG.ClassicalInvolution.RouteD.TypeCChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem routeD_typeC_of_layers (S : CSetup p f m Ω K z) (hconn : DeltaConnected Ω)
    (hL : ∀ Fr : Frame p f m Ω K z, LayersCommute Fr) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = m + 1 := by
  obtain ⟨Fr⟩ := exists_frame S
  exact routeD_typeC_of_chain S.odd S.five S.two_le S.inClass S.mem S.single hconn S.cls S.shape
    S.p1_z (chain S Fr) (by rw [chain_last]; exact Fr.mem _) (chain_comm S Fr (hL Fr))
    (chain_pair S Fr) (chain_sp S Fr)

theorem routeD_typeC (S : CSetupAll p f m Ω K z) (hconn : DeltaConnected Ω) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = m + 1 :=
  routeD_typeC_of_layers S.toCSetup hconn fun Fr =>
    layersCommute_of_block S.toCSetup S.p1 S.noOther Fr

theorem routeD_typeC_of_four (S : CSetup p f m Ω K z) (hm : 4 ≤ m) (hconn : DeltaConnected Ω) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = m + 1 :=
  routeD_typeC_of_layers S hconn fun Fr => layersCommute_of_five S hm Fr

end CFSG.ClassicalInvolution.RouteD
