module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Main
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Aux

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Hat2A7S

theorem dComp_subset_twinSet {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hperp : KPerp Ω K = twinSet Ω K) : dComp Ω K ⊆ twinSet Ω K := by
  intro J hJ
  induction hJ with
  | refl => exact mem_twinSet_self hK hz
  | @tail b c _ hbc ih =>
    obtain ⟨hc, hadj⟩ := hbc
    have hcb : c ∈ omegaNbr Ω b := by
      rcases hadj with h | h
      · exact h
      · exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hc ih.1 h
    have h1 : c ∈ KPerp Ω b := Set.mem_insert_of_mem _ hcb
    rwa [kPerp_eq_of_twin hΩ hK ih, hperp] at h1

end CFSG.ClassicalInvolution.A7T22
