module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace TwinThmE

section CoreSec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G}

variable (Ω w) in
@[expose] noncomputable def secEmb : ↥(coreHull Ω w) →* G :=
  (Subgroup.centralizer ({w} : Set G)).subtype.comp (coreHull Ω w).subtype

theorem secEmb_injective : Function.Injective (secEmb Ω w) :=
  Subtype.val_injective.comp Subtype.val_injective

variable (Ω w) in
noncomputable abbrev secOf (J : Subgroup G) : Subgroup ↥(coreHull Ω w) :=
  ((TwinADescent.coreAt w J).subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf
    (coreHull Ω w)

theorem map_secOf {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) :
    (secOf Ω w J).map (secEmb Ω w) = TwinADescent.coreAt w J := by
  unfold secEmb
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (le_coreHull hJ),
    Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer w J)]

theorem exists_of_mem_hullFam {L : Subgroup ↥(coreHull Ω w)} (hL : L ∈ hullFam Ω w) :
    ∃ J ∈ tqMembers3 Ω w, L = secOf Ω w J := by
  obtain ⟨_, ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩, -, rfl⟩ := hL
  exact ⟨J, hJ, rfl⟩

theorem secOf_mem_hullFam {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) :
    secOf Ω w J ∈ hullFam Ω w :=
  subgroupOf_mem_hullFam hJ

theorem mem_RSet_of_coreFamily (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {R : Subgroup G} (hR : R ∈ RSet (TwinADescent.coreFamily Ω w)) : R ∈ RSet Ω := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨J, hJ, rfl⟩ := hM
  exact mem_RSet_of_isSylow2In hJ.1 ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mp hRM).1

theorem mem_omegaNbr_of_coreFamily (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω w) (hJ : J ∈ tqMembers3 Ω w)
    (h : TwinADescent.coreAt w J ∈
      omegaNbr (TwinADescent.coreFamily Ω w) (TwinADescent.coreAt w K)) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨-, hne, R, hR, hRJ, hRN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  have hRΩ := mem_RSet_of_coreFamily hΩ hc2 hR
  have hRJG : R ≤ J := hRJ.trans (TwinADescent.coreAt_le_left w J)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := TwinDisc.isUniqueInvolution_coreAt_of_tq hΩ hc2 hK hz
  have hRc : R ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hRN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J', -, hRs⟩ := exists_isSylow2In_of_mem_RSet hRΩ
    exact hRs.2.1
  have hRN' : R ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 hJK.symm hz hRJG hR2 (by omega) hRc
  exact ⟨hJ.1, hJK, R, hRΩ, hRJG, hRN'⟩

theorem exists_lift_kPerp (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ tqMembers3 Ω w) {J : Subgroup ↥(coreHull Ω w)}
    (hJ : J ∈ KPerp (hullFam Ω w) (secOf Ω w L₀)) :
    ∃ J₀ ∈ tqMembers3 Ω w, J = secOf Ω w J₀ ∧ J₀ ∈ KPerp Ω L₀ := by
  rcases hJ with rfl | h
  · exact ⟨L₀, hL₀, rfl, Set.mem_insert _ _⟩
  · obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_hullFam h.1
    refine ⟨J₀, hJ₀, rfl, Set.mem_insert_of_mem _ ?_⟩
    have h1 := Asc77.omegaNbr_map h
    rw [Subgroup.map_subgroupOf_eq_of_le (le_coreHull hJ₀),
      Subgroup.map_subgroupOf_eq_of_le (le_coreHull hL₀)] at h1
    have h2 := Asc77.omegaNbr_map h1
    rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer w J₀),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer w L₀)] at h2
    exact mem_omegaNbr_of_coreFamily hΩ hc2 hL₀ hJ₀ h2

theorem hullFam_twoGroup (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    ∀ J ∈ hullFam Ω w, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
  intro J hJ
  obtain ⟨M, hM, rfl⟩ := exists_of_mem_hullFam hJ
  have h1 : IsPGroup 2 (↥(TwinADescent.coreAt w M) ⧸
      classicalInvolutionOddCore ↥(TwinADescent.coreAt w M)) :=
    TwinEdge.isPGroup_two_quotient_of_le (TwinADescent.coreAt_le_left w M) (h2 M hM.1)
  have h2C := isPGroup_two_quotient_subgroupOf (TwinADescent.coreAt w M)
    (Subgroup.centralizer ({w} : Set G)) h1
  exact isPGroup_two_quotient_subgroupOf
    ((TwinADescent.coreAt w M).subgroupOf (Subgroup.centralizer ({w} : Set G))) (coreHull Ω w) h2C

@[expose] def coreGood (Ω : Set (Subgroup G)) (w : G) (K : Subgroup G)
    (L : Subgroup ↥(coreHull Ω w)) : Prop :=
  ∃ J ∈ tqMembers3 Ω w, L = secOf Ω w J ∧ J ∈ dstarComp Ω K

theorem coreGood_step (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w)) {K : Subgroup G}
    {L L' : Subgroup ↥(coreHull Ω w)} (hL' : L' ∈ hullFam Ω w) (hgood : coreGood Ω w K L)
    (hadj : dstarAdj (hullFam Ω w) L L') : coreGood Ω w K L' := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', rfl⟩ := exists_of_mem_hullFam hL'
  exact ⟨J', hJ', rfl, hJK.tail (dstarAdj_of_hullFam hΩ hc2 hJ hJ' hadj)⟩

theorem coreGood_of_mem_dstarComp (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {K : Subgroup G} (hK : K ∈ tqMembers3 Ω w) {J : Subgroup ↥(coreHull Ω w)}
    (hJ : J ∈ dstarComp (hullFam Ω w) (secOf Ω w K)) : coreGood Ω w K J := by
  induction hJ with
  | refl => exact ⟨K, hK, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih => exact coreGood_step hΩ hc2 hbc.1 ih hbc

end CoreSec

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
