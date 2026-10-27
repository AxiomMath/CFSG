module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26VProper
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Odd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section Lambda

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem layerHull_sup_omegaNbrGen (Ω : Set (Subgroup G)) {K : Subgroup G} (hK : K ∈ Ω) :
    layerHull Ω (K ⊔ omegaNbrGen Ω K) = K ⊔ omegaNbrGen Ω K := by
  refine le_antisymm (iSup₂_le fun L _ => iSup_le fun hL => hL) ?_
  refine sup_le (le_layerHull hK le_sup_left) ?_
  refine iSup₂_le fun M hM => ?_
  exact le_layerHull hM.1 ((le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hM).trans
    le_sup_right)

theorem commutator_mem_oddCoreOf_lambda [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) :
    ∀ k ∈ K, ∀ x ∈ omegaNbrGen Ω K, ⁅k, x⁆ ∈ oddCoreOf (K ⊔ omegaNbrGen Ω K) := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  set Λ : Subgroup G := K ⊔ X with hΛdef
  have hKΛ : K ≤ Λ := le_sup_left
  have hXΛ : X ≤ Λ := le_sup_right
  have hΛN : Λ ≤ sigmaNorm Ω K :=
    sup_le (s26_le_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK Relation.ReflTransGen.refl)
      (s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK)
  have hΛp : Λ ≠ ⊤ := fun htop => by
    rw [htop, top_le_iff] at hΛN
    exact hdisc (dConnected_of_sigmaNorm_eq_top hK hs.stand.trans hΛN)
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥Λ)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Λ
  have hlt : Nat.card (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) < Nat.card G := by
    have h1 : Nat.card ↥Λ < Nat.card G :=
      lt_of_le_of_ne (Subgroup.card_le_card_group Λ)
        (fun h => hΛp (Subgroup.eq_top_of_card_eq Λ h))
    exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) h1
  have hGen : GenSection p f (oddQuotientFamily (restrictFamily Ω Λ)) := by
    have := genSection_layerHull hp hq hΩ hs.stand.aEmpty Λ
    rwa [layerHull_sup_omegaNbrGen Ω hK] at this
  have hK' : K.subgroupOf Λ ∈ restrictFamily Ω Λ := subgroupOf_mem_restrictFamily hK hKΛ
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) with hπ
  have hKb : (K.subgroupOf Λ).map π ∈ oddQuotientFamily (restrictFamily Ω Λ) := ⟨_, hK', rfl⟩
  obtain ⟨D⟩ := exists_omegaLie hn hGen.hyp ⟨_, hKb⟩ hGen.oddCore hlt
  have hΦ : HypOmega p f (oddQuotientFamily (restrictFamily Ω Λ)) :=
    hGen.hyp.toExact (D.exactMembers hp hq hGen.hyp)
  have hJX : ∀ J' ∈ omegaNbr Ω K, J' ≤ X := fun J' hJ' =>
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J' hJ'
  have hnbr : ∀ J' ∈ omegaNbr Ω K, (J'.subgroupOf Λ).map π ∈
      omegaNbr (oddQuotientFamily (restrictFamily Ω Λ)) ((K.subgroupOf Λ).map π) := by
    intro J' hJ'
    have hJ'Λ : J' ≤ Λ := (hJX J' hJ').trans hXΛ
    have h1 := omegaNbr_subgroupOf hp hΩ hKΛ hJ'Λ hJ'.1 hJ'
    obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ'.1
    refine T8S2.omegaNbr_map_odd hp (hΩ.restrict Λ) hNodd h1 ?_
    refine T8S2.map_ne_of_noTwins hp (hΩ.restrict Λ) hNodd
      (isUniqueInvolution_subgroupOf hs.hz hKΛ) (isUniqueInvolution_subgroupOf hzJ hJ'Λ)
      h1 ?_
    rintro ⟨-, z', hz'K, hz'J⟩
    have hJK : J' ∈ twinSet Ω K :=
      ⟨hJ'.1, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hKΛ,
        isUniqueInvolution_of_subgroupOf hz'J hJ'Λ⟩
    rw [hs.noTwins J' hJK]
  have hcomm : ∀ J' ∈ omegaNbr Ω K,
      Commutes ((K.subgroupOf Λ).map π) ((J'.subgroupOf Λ).map π) := fun J' hJ' =>
    AscE186.commutes_of_mem_omegaNbr hp hq hΦ hKb (hnbr J' hJ')
  have hXC : X ≤ ((Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))).comap
      π).map Λ.subtype := by
    refine iSup₂_le fun J' hJ' j hj => ?_
    have hJ'Λ : J' ≤ Λ := (hJX J' hJ').trans hXΛ
    refine ⟨⟨j, hJ'Λ hj⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm J' hJ' b hb _
      ⟨⟨j, hJ'Λ hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  intro k hk x hx
  have hkΛ : k ∈ Λ := hKΛ hk
  have hxΛ : x ∈ Λ := hXΛ hx
  have hxC : π ⟨x, hxΛ⟩ ∈ Subgroup.centralizer (((K.subgroupOf Λ).map π : Subgroup (↥Λ ⧸
      classicalInvolutionOddCore ↥Λ)) : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) := by
    obtain ⟨y, hy, hyx⟩ := hXC hx
    have hyeq : y = ⟨x, hxΛ⟩ := Subtype.ext hyx
    rw [hyeq] at hy
    exact hy
  have hcomm2 : π ⟨k, hkΛ⟩ * π ⟨x, hxΛ⟩ = π ⟨x, hxΛ⟩ * π ⟨k, hkΛ⟩ :=
    Subgroup.mem_centralizer_iff.mp hxC _
      ⟨⟨k, hkΛ⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hmem1 : π ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm2
  have hmem2 : ⁅(⟨k, hkΛ⟩ : ↥Λ), (⟨x, hxΛ⟩ : ↥Λ)⁆ ∈ classicalInvolutionOddCore ↥Λ :=
    (QuotientGroup.eq_one_iff _).mp hmem1
  exact ⟨_, hmem2, by simp [commutatorElement_def]⟩

theorem commute_of_mem_two_subgroup [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) {P : Subgroup G} (hP : IsPGroup 2 ↥P) {k x : G} (hk : k ∈ K)
    (hx : x ∈ omegaNbrGen Ω K) (hkP : k ∈ P) (hxP : x ∈ P) : k * x = x * k := by
  have h1 := commutator_mem_oddCoreOf_lambda hs hdisc k hk x hx
  have hmemP : ⁅k, x⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hkP hxP) (P.inv_mem hkP)) (P.inv_mem hxP)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅k, x⁆) := hP.to_le (Subgroup.zpowers_le.mpr hmemP)
  have h2 : ⁅k, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1 hpg
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Lambda

end T8W

end CFSG.ClassicalInvolution.Asc77
