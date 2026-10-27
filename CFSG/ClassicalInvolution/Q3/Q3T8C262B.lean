module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Comm
import CFSG.ClassicalInvolution.Asc77.AscT8S2MainEng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8S2
open CFSG.ClassicalInvolution.Asc77.T8S2
section Q
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem not_le_omegaNbrGen (hs : Std8 Ω K J S R T W z t) (hX : omegaNbrGen Ω K ≠ ⊤) :
    ¬ K ≤ omegaNbrGen Ω K := by
  intro hKX
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hn : Generic.CITBelowU (Nat.card G) := hs.stand.below
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < Nat.card G := by
    have h1 : Nat.card ↥X < Nat.card G :=
      lt_of_le_of_ne (Subgroup.card_le_card_group X)
        (fun h => hX (Subgroup.eq_top_of_card_eq X h))
    exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) h1
  have hK' : K.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hK hKX
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
  have hKb : (K.subgroupOf X).map π ∈ oddQuotientFamily (restrictFamily Ω X) := ⟨_, hK', rfl⟩
  
  have hΦ : HypOmega (oddQuotientFamily (restrictFamily Ω X)) :=
    Sect.hypOmega_section_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty hn hX ⟨_, hK'⟩
  
  have hJX : ∀ J' ∈ omegaNbr Ω K, J' ≤ X := fun J' hJ' =>
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J' hJ'
  have hnbr : ∀ J' ∈ omegaNbr Ω K, (J'.subgroupOf X).map π ∈
      omegaNbr (oddQuotientFamily (restrictFamily Ω X)) ((K.subgroupOf X).map π) := by
    intro J' hJ'
    have h1 := C25J.omegaNbr_subgroupOf_gen hΩ hKX (hJX J' hJ') hJ'.1 hJ'
    obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hJ'.1
    refine omegaNbr_map_odd (Sect.hypOmegaGen_restrict hs.stand.modU X) hNodd h1 ?_
    refine map_ne_of_noTwins (Sect.hypOmegaGen_restrict hs.stand.modU X) hNodd
      (isUniqueInvolution_subgroupOf hs.hz hKX) (isUniqueInvolution_subgroupOf hzJ (hJX J' hJ'))
      h1 ?_
    rintro ⟨-, z', hz'K, hz'J⟩
    have hJK : J' ∈ twinSet Ω K :=
      ⟨hJ'.1, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hKX,
        isUniqueInvolution_of_subgroupOf hz'J (hJX J' hJ')⟩
    rw [hs.noTwins J' hJK]
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hRK : R ≤ K := hs.hR.2.1
  have hRX : R ≤ X := hRK.trans hKX
  have hRb : IsSylow2In ((R.subgroupOf X).map π) ((K.subgroupOf X).map π) :=
    isSylow2In_map_mk hNodd (hRsyl.subgroupOf hKX)
  have hcomm : ∀ J' ∈ omegaNbr Ω K,
      Commutes ((R.subgroupOf X).map π) ((J'.subgroupOf X).map π) := fun J' hJ' =>
    AscE186.commutes_sylow_of_mem_omegaNbr hΦ hKb (hnbr J' hJ') hRb
  
  have hXC : X ≤ ((Subgroup.centralizer (((R.subgroupOf X).map π : Subgroup (↥X ⧸
      classicalInvolutionOddCore ↥X)) : Set (↥X ⧸ classicalInvolutionOddCore ↥X))).comap
      π).map X.subtype := by
    refine iSup₂_le fun J' hJ' j hj => ?_
    refine ⟨⟨j, hJX J' hJ' hj⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm J' hJ' b hb _
      ⟨⟨j, hJX J' hJ' hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  
  obtain ⟨a, ha, c, hc, hac⟩ := (hΩ.isQuatSub_of_mem_RSet hs.hR.1).exists_not_commute
  have haX : a ∈ X := hRX ha
  have hcX : c ∈ X := hRX hc
  have hcC : π ⟨c, hcX⟩ ∈ Subgroup.centralizer (((R.subgroupOf X).map π : Subgroup (↥X ⧸
      classicalInvolutionOddCore ↥X)) : Set (↥X ⧸ classicalInvolutionOddCore ↥X)) := by
    obtain ⟨y, hy, hyc⟩ := hXC hcX
    have hyeq : y = ⟨c, hcX⟩ := Subtype.ext hyc
    rw [hyeq] at hy
    exact hy
  have hcomm2 : π ⟨a, haX⟩ * π ⟨c, hcX⟩ = π ⟨c, hcX⟩ * π ⟨a, haX⟩ :=
    Subgroup.mem_centralizer_iff.mp hcC _
      ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hmem1 : π ⁅(⟨a, haX⟩ : ↥X), (⟨c, hcX⟩ : ↥X)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm2
  have hmem2 : ⁅(⟨a, haX⟩ : ↥X), (⟨c, hcX⟩ : ↥X)⁆ ∈ classicalInvolutionOddCore ↥X :=
    (QuotientGroup.eq_one_iff _).mp hmem1
  have h1 : ⁅a, c⁆ ∈ oddCoreOf X := ⟨_, hmem2, by simp [commutatorElement_def]⟩
  have hmemR : ⁅a, c⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hc) (R.inv_mem ha)) (R.inv_mem hc)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅a, c⁆) :=
    hRsyl.2.1.to_le (Subgroup.zpowers_le.mpr hmemR)
  have h2 : ⁅a, c⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h1 hpg
  exact hac (commutatorElement_eq_one_iff_mul_comm.mp h2)

end Q
end T8S2
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_sylow_meeting_X (hs : Std8 Ω K J S R T W z t) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  exact CFSG.ClassicalInvolution.Asc77.exists_sylow_meeting_XE hs.hR.2.1
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1)
    (s26_conjSub_omegaNbrGen hΩ)

theorem s26XMuZ2_of_data (hs : Std8 Ω K J S R T W z t)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (hX : omegaNbrGen Ω K ≠ ⊤) :
    ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
      MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W' := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨S₂, hRS₂, hS₂X⟩ := exists_sylow_meeting_X hs
  obtain ⟨J₂, hJ₂, hK1⟩ :=
    T8S2.exists_unique_member hs φ hRS₂ (T8S2.not_le_omegaNbrGen hs hX)
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hs.stand.modU hs.stand.aEmpty
  have hJ₂X : J₂ ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J₂ hJ₂
  refine T8S2.exists_muIsoZ2_of_sylow (Λ := restrictFamily Ω X) (Sect.hypOmegaGen_restrict
      hs.stand.modU X)
    ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩ (AscP1Nine3.sylowOfIsSylow2In₉ hS₂X) (J₀ := J₂.subgroupOf X)
    ⟨J₂, hJ₂.1, hJ₂X, rfl⟩ ?_
  rintro _ ⟨L, hL, hLX, rfl⟩ hcard
  have hSH : ((AscP1Nine3.sylowOfIsSylow2In₉ hS₂X : Sylow 2 ↥X) : Subgroup ↥X) =
      ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have hLS : L ⊓ (S₂ : Subgroup G) ≤ X := inf_le_left.trans hLX
  have hinf : L.subgroupOf X ⊓ ((S₂ : Subgroup G) ⊓ X).subgroupOf X =
      (L ⊓ (S₂ : Subgroup G)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hSH, hinf] at hcard
  have hc2 : Nat.card ↥((L ⊓ (S₂ : Subgroup G)).subgroupOf X) =
      Nat.card ↥(L ⊓ (S₂ : Subgroup G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
  rw [hc2] at hcard
  rw [hK1 L hL hLX hcard]

theorem s26XMuZ2_proved : S26XMuZ2 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨φ⟩ := hS4
  exact s26XMuZ2_of_data hs φ (s26XProper_proved G Ω K J S R T W z t hs hdisc ⟨φ⟩)
end Main
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
