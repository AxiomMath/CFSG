module

public import CFSG.ClassicalInvolution.Q3.TL3T60

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G]

variable {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

theorem oddCore_centMembers_eq_bot {u : G} {R : Subgroup G} (hRn : R.Normal)
    (hR2 : IsPGroup 2 ↥R) (huR : u ∈ R) :
    classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥ := by
  have h1 := oddCoreImg_centralizer_eq_bot hS.cex.odd hRn hR2 huR
  have hN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G) := by
    intro c hc
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcu' : c⁻¹ * u = u * c⁻¹ :=
      calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * u) * c⁻¹ := by rw [hcu]
        _ = u * c⁻¹ := by group
    exact mem_normalizer_pSpan (fun L hL => hS.conjSub_mem_centMembers_of_comm hcu hL)
      (fun L hL => hS.conjSub_mem_centMembers_of_comm hcu' hL)
  have h2 := oddCoreImg_le_of_le_normalizer (pSpan_centMembers_le u) hN
  rw [h1] at h2
  exact oddCore_eq_bot_of_oddCoreImg (le_bot_iff.mp h2)

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin
