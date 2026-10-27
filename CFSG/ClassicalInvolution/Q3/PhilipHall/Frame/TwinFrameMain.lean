module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.TL4SepDefs
public import CFSG.ClassicalInvolution.SmallCases.A7Q1C

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4

namespace TwinFrame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_frame (hΩ : HypOmegaGen Ω) (hconn : DConnected Ω) (hgen : (⨆ J ∈ Ω, J) = ⊤)
    (hZ : Subgroup.center G = ⊥) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) :
    ∃ (u : G) (J : Subgroup G) (t : G), TwinFrameData Ω K K' z u J t := by
  by_contra hcon
  have hperp : KPerp Ω K = twinSet Ω K := by
    by_contra hne'
    exact hcon (A7Q.Gen.exists_twinFrameData hΩ hK hz hK' hne hne')
  have hall : ∀ N : Subgroup G,
      Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ dAdj Ω X Y) K N →
        N ∈ twinSet Ω K := by
    intro N hpath
    induction hpath with
    | refl => exact mem_twinSet_self hK hz
    | @tail b c _ hstep ih =>
      obtain ⟨hcΩ, hadj⟩ := hstep
      have hbΩ : b ∈ Ω := ih.1
      have hperpb : KPerp Ω b = twinSet Ω K := by
        rw [← A7Q.Gen.kPerp_eq_of_twin hΩ hK ih, hperp]
      have hc : c ∈ KPerp Ω b := by
        rcases hadj with hbc | hcb
        · exact Set.mem_insert_of_mem _ hbc
        · exact Set.mem_insert_of_mem _
            (Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ hcb)
      rwa [hperpb] at hc
  have hC : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({z} : Set G) := by
    refine iSup₂_le fun N hN => ?_
    have hNt : N ∈ twinSet Ω K := hall N (hconn K hK N hN)
    exact le_centralizer_of_unique (isUniqueInvolution_of_mem_twinSet hz hNt)
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := hC (hgen ▸ Subgroup.mem_top g)
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hz.ne_one hzc

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
