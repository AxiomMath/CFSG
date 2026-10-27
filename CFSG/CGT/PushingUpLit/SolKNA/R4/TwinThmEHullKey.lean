module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWRestrict
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section HullKey


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G}

theorem hullpf_inf_le_coreAt {J : Subgroup G}
    (hJ : w ∈ Balance.Bootstrap.trivialOnQuot J) {S' : Sylow 2 G}
    (hwS : w ∈ (S' : Subgroup G)) : J ⊓ (S' : Subgroup G) ≤ TwinADescent.coreAt w J := by
  have hcomm : ∀ a ∈ J ⊓ (S' : Subgroup G), a ∈ Subgroup.centralizer ({w} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅w, a⁆ ∈ Balance.oddCoreIn J :=
      (Balance.Bootstrap.mem_trivialOnQuot_iff.mp hJ).2 a ha.1
    have h2 : ⁅w, a⁆ ∈ (S' : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S' : Subgroup G).mul_mem ((S' : Subgroup G).mul_mem
        ((S' : Subgroup G).mul_mem hwS ha.2) ((S' : Subgroup G).inv_mem hwS))
        ((S' : Subgroup G).inv_mem ha.2)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅w, a⁆) :=
      S'.isPGroup'.to_le (Subgroup.zpowers_le.mpr h2)
    have h4 := eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn J) h1 h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm
  exact le_tightCore_of_isPGroup (fun a ha => ⟨ha.1, hcomm a ha⟩)
    (S'.isPGroup'.to_le inf_le_right)

theorem hullpf_mem_sylow_of_mem {S' : Sylow 2 G} {S₁ : Sylow 2 ↥(coreHull Ω w)}
    (hS₁ : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G))
    {x : ↥(coreHull Ω w)} (hx : secEmb Ω w x ∈ (S' : Subgroup G)) :
    x ∈ (S₁ : Subgroup ↥(coreHull Ω w)) := by
  have h2 : IsPGroup 2 ↥((S' : Subgroup G).comap (secEmb Ω w)) :=
    S'.isPGroup'.comap_of_injective _ secEmb_injective
  have hle : (S₁ : Subgroup ↥(coreHull Ω w)) ≤ (S' : Subgroup G).comap (secEmb Ω w) :=
    fun y hy => hS₁ ⟨y, hy, rfl⟩
  have heq := S₁.is_maximal' h2 hle
  have hx' : x ∈ (S' : Subgroup G).comap (secEmb Ω w) := hx
  rw [heq] at hx'
  exact hx'

theorem hullpf_map_mem_USet (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {V : Subgroup ↥(coreHull Ω w)} (hV : V ∈ USet (hullFam Ω w)) :
    V.map (secEmb Ω w) ∈ USet Ω := by
  have h1 := map_mem_USet_restrict hV
  have h2 := map_mem_USet_restrict h1
  have e : V.map (secEmb Ω w) =
      (V.map (coreHull Ω w).subtype).map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e]
  exact TwinADescent.mem_USet_of_core hc2 h2

theorem hullpf_map_mem_RSet (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {P : Subgroup ↥(coreHull Ω w)} (hP : P ∈ RSet (hullFam Ω w)) :
    P.map (secEmb Ω w) ∈ RSet Ω := by
  have h1 := map_mem_RSet_restrict hP
  have h2 := map_mem_RSet_restrict h1
  have e : P.map (secEmb Ω w) =
      (P.map (coreHull Ω w).subtype).map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e]
  obtain ⟨L, hL, hPL⟩ := exists_isSylow2In_of_mem_RSet h2
  obtain ⟨K, hK, rfl⟩ := hL
  exact mem_RSet_of_isSylow2In hK.1 (((TwinADescent.isSylow2In_coreAt_iff hc2 hK.2).mp hPL).1)

theorem hullpf_mem_USet_hullFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {J P U : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) (hP : IsSylow2In P (TwinADescent.coreAt w J))
    (hUP : U ≤ P) (hcyc : IsCyclic ↥U) (hidx : U.relIndex P = 2) :
    ((U.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) ∈
      USet (hullFam Ω w) := by
  have hcore : TwinADescent.coreAt w J ∈ TwinADescent.coreFamily Ω w :=
    TwinADescent.coreAt_mem_coreFamily hJ
  have hU1 : U.subgroupOf (Subgroup.centralizer ({w} : Set G)) ∈
      USet (restrictFamily (TwinADescent.coreFamily Ω w) (Subgroup.centralizer ({w} : Set G))) :=
    CFSG.ClassicalInvolution.Asc77.AscAET.mem_USet_restrict_of_sylow hcore
      (TwinADescent.coreAt_le_centralizer w J) hP hUP hcyc hidx
  exact mem_USet_restrict_of_le (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) hU1
    (subgroupOf_mem_restrictFamily hcore (TwinADescent.coreAt_le_centralizer w J))
    (le_coreHull hJ) (Subgroup.subgroupOf_mono _ (hUP.trans hP.1))

theorem hullpf_map_lift {J A : Subgroup G} (hJ : J ∈ tqMembers3 Ω w)
    (hA : A ≤ TwinADescent.coreAt w J) :
    ((A.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)).map
      (secEmb Ω w) = A := by
  have hAC : A ≤ Subgroup.centralizer ({w} : Set G) :=
    hA.trans (TwinADescent.coreAt_le_centralizer w J)
  have hAX : A.subgroupOf (Subgroup.centralizer ({w} : Set G)) ≤ coreHull Ω w :=
    (Subgroup.subgroupOf_mono _ hA).trans (le_coreHull hJ)
  unfold secEmb
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAX,
    Subgroup.map_subgroupOf_eq_of_le hAC]

theorem hullpf_map_le {M : Subgroup G} (hM : M ∈ tqMembers3 Ω w)
    {V : Subgroup ↥(coreHull Ω w)} (hV : V ≤ secOf Ω w M) :
    V.map (secEmb Ω w) ≤ TwinADescent.coreAt w M := by
  have := Subgroup.map_mono (f := secEmb Ω w) hV
  rwa [map_secOf hM] at this

theorem hullpf_key (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {S' : Sylow 2 G} {W' : Subgroup G} (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hwS : w ∈ (S' : Subgroup G)) {S₁ : Sylow 2 ↥(coreHull Ω w)}
    (hS₁ : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G))
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) {V : Subgroup ↥(coreHull Ω w)}
    (hV : V ∈ USet (hullFam Ω w)) (hVS₁ : V ≤ (S₁ : Subgroup ↥(coreHull Ω w)))
    (hVJ : V ≤ secOf Ω w J) :
    J ⊓ W' ∈ USet Ω ∧ J ⊓ W' ≤ TwinADescent.coreAt w J ∧
      ((J ⊓ W').subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w) ∈
        USet (hullFam Ω w) := by
  have hVU : V.map (secEmb Ω w) ∈ USet Ω := hullpf_map_mem_USet hc2 hV
  have hVmapJ : V.map (secEmb Ω w) ≤ TwinADescent.coreAt w J := hullpf_map_le hJ hVJ
  have hVS' : V.map (secEmb Ω w) ≤ (S' : Subgroup G) := (Subgroup.map_mono hVS₁).trans hS₁
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have hcard : 2 < Nat.card ↥(J ⊓ (S' : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf (hVmapJ.trans (TwinADescent.coreAt_le_left w J)) hVS')
    omega
  have hUinf : J ⊓ W' ∈ USet Ω := inf_W_mem_USet_of_card hΩ hW' hW'S hJ.1 hcard
  have hUcore : J ⊓ (S' : Subgroup G) ≤ TwinADescent.coreAt w J :=
    hullpf_inf_le_coreAt hJ.2 hwS
  have hUle : J ⊓ W' ≤ TwinADescent.coreAt w J := (inf_le_inf_left J hW'S).trans hUcore
  obtain ⟨R', -, J', hJ'Ω, hR'J', hUR', hUcyc, hR'card, hU4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hUinf
  have hU2 : IsPGroup 2 ↥(J ⊓ W') := Sec6Gen.isPGroup_of_mem_USet hΩ hUinf
  have hJJ' : J' = J :=
    Sec6Gen.eq_of_le_of_le hΩ hJ'Ω hJ.1 hU2 hU4 (hUR'.trans hR'J'.1) inf_le_left
  have hR'J : IsSylow2In R' J := hJJ' ▸ hR'J'
  obtain ⟨P, hP, hUP⟩ := IsSylow2In.exists_ge hU2 hUle
  have hPJ : IsSylow2In P J := ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mp hP).1
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥(J ⊓ W') := by
    rw [hPJ.natCard_eq hR'J, hR'card]
  have hidx : (J ⊓ W').relIndex P = 2 :=
    CFSG.ClassicalInvolution.Asc77.AscAET.relIndex_eq_two_of_card hUP hPcard
  exact ⟨hUinf, hUle, hullpf_mem_USet_hullFam hΩ hc2 hJ hP hUP hUcyc hidx⟩

end HullKey

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
