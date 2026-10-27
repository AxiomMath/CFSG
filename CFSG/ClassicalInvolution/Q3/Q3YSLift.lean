module

public import CFSG.ClassicalInvolution.Q3.Q3ABoot
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Balance.GoodDataBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem fourGroup_mem_of_not_bootData3 [Finite G] {Ω : Set (Subgroup G)} (hex : ExactMembers3 Ω)
    {z : G} (hP1 : LocalOddCentral Ω {z}) (hO3 : Q3W.LocalOddThreeFree3 Ω z)
    (hB : ¬ BootData3 Ω) {K : Subgroup G} (hKΩ : K ∈ Ω) (hz : IsClassicalMember3 K z)
    {F : Subgroup (locQuot Ω z)} (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 4)
    (hc : ∀ f ∈ F, ∀ k ∈ locImg Ω z K, f * k = k * f) :
    ∃ hzY : z ∈ locLayer Ω z,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hzY⟩ ∈ F := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hKΩ, isSubnormal_le hz.subnormal⟩
  have hKY : K ≤ locLayer Ω z := le_centralizingLayer hKz
  have hzY : z ∈ locLayer Ω z := hKY hz.mem
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥(locLayer Ω z))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(locLayer Ω z)
  obtain ⟨H, hH, hHF, hHcard⟩ :=
    Balance.GoodData.exists_isElemAbelian_lift_map
      (classicalInvolutionOddCore ↥(locLayer Ω z)) hNodd F hF
  have hH'card : Nat.card (H.map (locLayer Ω z).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective (locLayer Ω z)), hHcard,
      hcard]
  have hsq : ∀ x ∈ H.map (locLayer Ω z).subtype, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hH.2 x hx
    rw [pow_two] at this
    exact congrArg Subtype.val this
  have hcomm : ∀ x ∈ H.map (locLayer Ω z).subtype, ∀ y ∈ H.map (locLayer Ω z).subtype,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hH.1.is_comm.comm (⟨x, hx⟩ : H) ⟨y, hy⟩
    exact congrArg (fun t : H => ((t : ↥(locLayer Ω z)) : G)) this
  have hbot : ⁅K.subgroupOf (locLayer Ω z), H⁆ = ⊥ := by
    refine Q3.commutes_of_equiv_sl2Three hP1 hO3 ?_ ?_
    · obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex K hKΩ)
      exact ⟨(Subgroup.subgroupOfEquivOfLe hKY).trans e⟩
    · intro a ha b hb
      rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω z))]
      change QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      have hbF : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) b ∈ F := by
        rw [← hHF]
        exact ⟨b, hb, rfl⟩
      exact (hc _ hbF _ ⟨a, ha, rfl⟩).symm
  have hcent : K ≤ Subgroup.centralizer
      ((H.map (locLayer Ω z).subtype : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have h2 := Subgroup.mem_centralizer_iff.mp
      (h1 (Subgroup.mem_subgroupOf.mpr hk :
        (⟨k, hKY hk⟩ : ↥(locLayer Ω z)) ∈ K.subgroupOf (locLayer Ω z))) x hx
    exact congrArg Subtype.val h2
  have hzH' : z ∈ H.map (locLayer Ω z).subtype :=
    mem_fourGroup_of_not_bootData3 hB hKΩ hz hsq hcomm hH'card hcent
  obtain ⟨x, hxH, hxz⟩ := hzH'
  have hx : x = ⟨z, hzY⟩ := Subtype.ext hxz
  refine ⟨hzY, ?_⟩
  rw [← hHF]
  exact ⟨x, hxH, by rw [hx]⟩

end CFSG.ClassicalInvolution.Q3.Q3YS
