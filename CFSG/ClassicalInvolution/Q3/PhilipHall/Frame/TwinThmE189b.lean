module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmE

section B

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isSubnormal_subgroupOf_gen {A B : Subgroup G} (h : IsSubnormal A B) (Y : Subgroup G) :
    IsSubnormal (A.subgroupOf Y) (B.subgroupOf Y) :=
  h.comap Y.subtype

theorem classicalClause_restrict (hcls : Q3CL.ClassicalClause Ω) (Y : Subgroup G) :
    Q3CL.ClassicalClause (restrictFamily Ω Y) where
  subnormal := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hzL, hz2, hsub⟩ := hcls.subnormal L hL
    have hzY : z ∈ Y := hLY hzL
    refine ⟨⟨z, hzY⟩, hzL, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]; exact hz2
    · have e : (Subgroup.centralizer ({z} : Set G)).subgroupOf Y =
          Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h; exact Subtype.ext (by simpa using h)
        · intro h; simpa using congrArg Subtype.val h
      rw [← e]
      exact isSubnormal_subgroupOf_gen hsub Y
  commOdd := by
    rintro _ ⟨J, hJ, hJY, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    have hu2' : IsPGroup 2 (Subgroup.zpowers (u : G)) := isPGroup_zpowers_coe_iff.mpr hu2
    have huu' : (u : G) * u ≠ 1 := fun h => huu (Subtype.ext h)
    have := hcls.commOdd J hJ (u : G) (a : G) (b : G) hu hu2' huu' ha hb (congrArg Subtype.val hau)
      (congrArg Subtype.val hbu)
    rw [oddCoreOf_subgroupOf hJY]
    exact this

theorem two_restrict (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (Y : Subgroup G) :
    ∀ L ∈ restrictFamily Ω Y, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  rintro _ ⟨L, hL, hLY, rfl⟩
  let φ : ↥(L.subgroupOf Y) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  exact (h2 L hL).of_equiv (QuotientGroup.congr _ _ φ
    (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm

theorem q8_restrict
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (Y : Subgroup G) :
    ∀ L ∈ restrictFamily Ω Y,
      ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨L, hL, hLY, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq8 L hL
  exact ⟨P.subgroupOf Y, hP.subgroupOf hLY,
    ⟨(Subgroup.subgroupOfEquivOfLe (hP.1.trans hLY)).trans e⟩⟩

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

end B

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
