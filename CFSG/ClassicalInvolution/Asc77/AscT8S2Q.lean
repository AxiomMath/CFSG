module

public import CFSG.ClassicalInvolution.Asc77.AscT8S2Odd
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VMu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8S2

section Q

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem not_le_omegaNbrGen (hs : Std8 p f Ω K J S R T W z t) (hX : omegaNbrGen Ω K ≠ ⊤) :
    ¬ K ≤ omegaNbrGen Ω K := by
  intro hKX
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hGen := s26_genSection_omegaNbrGen (K := K) hp hq hΩ hs.stand.aEmpty
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
  obtain ⟨D⟩ := exists_omegaLie hn hGen.hyp ⟨_, hKb⟩ hGen.oddCore hlt
  have hΦ : HypOmega p f (oddQuotientFamily (restrictFamily Ω X)) :=
    hGen.hyp.toExact (D.exactMembers hp hq hGen.hyp)
  have hJX : ∀ J' ∈ omegaNbr Ω K, J' ≤ X := fun J' hJ' =>
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J' hJ'
  have hnbr : ∀ J' ∈ omegaNbr Ω K, (J'.subgroupOf X).map π ∈
      omegaNbr (oddQuotientFamily (restrictFamily Ω X)) ((K.subgroupOf X).map π) := by
    intro J' hJ'
    have h1 := omegaNbr_subgroupOf hp hΩ hKX (hJX J' hJ') hJ'.1 hJ'
    obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ'.1
    refine omegaNbr_map_odd hp (hΩ.restrict X) hNodd h1 ?_
    refine map_ne_of_noTwins hp (hΩ.restrict X) hNodd
      (isUniqueInvolution_subgroupOf hs.hz hKX) (isUniqueInvolution_subgroupOf hzJ (hJX J' hJ'))
      h1 ?_
    rintro ⟨-, z', hz'K, hz'J⟩
    have hJK : J' ∈ twinSet Ω K :=
      ⟨hJ'.1, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hKX,
        isUniqueInvolution_of_subgroupOf hz'J (hJX J' hJ')⟩
    rw [hs.noTwins J' hJK]
  have hcomm : ∀ J' ∈ omegaNbr Ω K,
      Commutes ((K.subgroupOf X).map π) ((J'.subgroupOf X).map π) := fun J' hJ' =>
    AscE186.commutes_of_mem_omegaNbr hp hq hΦ hKb (hnbr J' hJ')
  have hXC : X ≤ ((Subgroup.centralizer (((K.subgroupOf X).map π : Subgroup (↥X ⧸
      classicalInvolutionOddCore ↥X)) : Set (↥X ⧸ classicalInvolutionOddCore ↥X))).comap
      π).map X.subtype := by
    refine iSup₂_le fun J' hJ' j hj => ?_
    refine ⟨⟨j, hJX J' hJ' hj⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm J' hJ' b hb _
      ⟨⟨j, hJX J' hJ' hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1
  have hRK : R ≤ K := hs.hR.2.1
  obtain ⟨a, ha, c, hc, hac⟩ := (hΩ.isQuatSub_of_mem_RSet hp hs.hR.1).exists_not_commute
  have haX : a ∈ X := hKX (hRK ha)
  have hcX : c ∈ X := hKX (hRK hc)
  have hcC : π ⟨c, hcX⟩ ∈ Subgroup.centralizer (((K.subgroupOf X).map π : Subgroup (↥X ⧸
      classicalInvolutionOddCore ↥X)) : Set (↥X ⧸ classicalInvolutionOddCore ↥X)) := by
    obtain ⟨y, hy, hyc⟩ := hXC hcX
    have hyeq : y = ⟨c, hcX⟩ := Subtype.ext hyc
    rw [hyeq] at hy
    exact hy
  have hcomm2 : π ⟨a, haX⟩ * π ⟨c, hcX⟩ = π ⟨c, hcX⟩ * π ⟨a, haX⟩ :=
    Subgroup.mem_centralizer_iff.mp hcC _
      ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr (hRK ha), rfl⟩
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

end CFSG.ClassicalInvolution.Asc77
