module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSec
public import CFSG.ClassicalInvolution.Asc77.AscIHSectF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

@[expose] def sylFamA (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set (Subgroup (SecQuot (rLayerSub Ω A))) :=
  {L | ∃ R' ∈ RSet Ω, R' ≤ Subgroup.centralizer (A : Set G) ∧ L = secImage (rLayerSub Ω A) R'}

@[expose] def SecCoresTwoGroup (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop :=
  ∀ J ∈ Ω, (∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G)) →
    IsPGroup 2 ↥(secImage (rLayerSub Ω A) (tightCore (J ⊓ Subgroup.centralizer (A : Set G))))

theorem secImage_syl_eq_core {J P : Subgroup G} (hJ : J ∈ Ω) (hP : IsSylow2In P J)
    (hPC : P ≤ Subgroup.centralizer (A : Set G))
    (h2 : IsPGroup 2 ↥(secImage (rLayerSub Ω A) (tightCore (J ⊓ Subgroup.centralizer (A : Set G))))) :
    secImage (rLayerSub Ω A) P =
      secImage (rLayerSub Ω A) (tightCore (J ⊓ Subgroup.centralizer (A : Set G))) := by
  have hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G) := ⟨P, hP, hPC⟩
  have hPs : IsSylow2In P (tightCore (J ⊓ Subgroup.centralizer (A : Set G))) :=
    (isSylow2In_core_iff hJC).mpr ⟨hP, hPC⟩
  have hcX : tightCore (J ⊓ Subgroup.centralizer (A : Set G)) ≤ rLayerSub Ω A :=
    core_le_rLayerSub hJ hJC
  have hs1 : IsSylow2In (P.subgroupOf (rLayerSub Ω A))
      ((tightCore (J ⊓ Subgroup.centralizer (A : Set G))).subgroupOf (rLayerSub Ω A)) :=
    hPs.subgroupOf hcX
  have hs2 := isSylow2In_map_mk (N := classicalInvolutionOddCore ↥(rLayerSub Ω A))
    (CFSG.ComponentClassification.OddCore.odd_card ↥(rLayerSub Ω A)) hs1
  exact (hs2.2.2 _ le_rfl h2 hs2.1).symm

theorem sylFamA_eq_secFamA (h : SecCoresTwoGroup Ω A) : sylFamA Ω A = secFamA Ω A := by
  ext L
  constructor
  · rintro ⟨R', hR', hRC, rfl⟩
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR'
    have hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G) :=
      ⟨R', hRJ, hRC⟩
    rw [secImage_syl_eq_core hJ hRJ hRC (h J hJ hJC)]
    exact ⟨_, ⟨_, ⟨J, hJ, hJC, rfl⟩, core_le_rLayerSub hJ hJC, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨J, hJ, hJC, rfl⟩, hLX, rfl⟩, rfl⟩
    obtain ⟨P, hP, hPC⟩ := hJC
    refine ⟨P, mem_RSet_of_isSylow2In hJ hP, hPC, ?_⟩
    exact (secImage_syl_eq_core hJ hP hPC (h J hJ ⟨P, hP, hPC⟩)).symm

theorem sylFamA_hypOmegaGen (hΩ : HypOmegaGen Ω) (h : SecCoresTwoGroup Ω A) :
    HypOmegaGen (sylFamA Ω A) := by
  rw [sylFamA_eq_secFamA h]
  exact hypOmegaGen_secFamA hΩ

theorem sylFamA_aEmpty (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hA2 : IsPGroup 2 ↥A)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) (h : SecCoresTwoGroup Ω A) :
    ∀ L ∈ sylFamA Ω A, AEmpty (sylFamA Ω A) L := by
  rw [sylFamA_eq_secFamA h]
  exact aEmpty_secFamA hΩ hA hA2 h2

theorem sylFamA_isPGroup (h : SecCoresTwoGroup Ω A) : ∀ L ∈ sylFamA Ω A, IsPGroup 2 ↥L := by
  rintro _ ⟨R', hR', hRC, rfl⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G) :=
    ⟨R', hRJ, hRC⟩
  rw [secImage_syl_eq_core hJ hRJ hRC (h J hJ hJC)]
  exact h J hJ hJC

theorem sylFamA_q8 (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (h : SecCoresTwoGroup Ω A) : ∀ L ∈ sylFamA Ω A, Nonempty (↥L ≃* QuaternionGroup 2) := by
  intro L hL
  have hL' : L ∈ secFamA Ω A := (sylFamA_eq_secFamA h) ▸ hL
  have h2 := sylFamA_isPGroup h L hL
  have hS : IsSylow2In L L := ⟨le_rfl, h2, fun V' hV' _ hLV' => le_antisymm hV' hLV'⟩
  obtain ⟨e⟩ := secFamA_q8 hq L hL' L hS
  exact ⟨(MulEquiv.refl _).trans e⟩

theorem sylFamA_card (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (h : SecCoresTwoGroup Ω A) : ∀ L ∈ sylFamA Ω A, Nat.card ↥L = 2 ^ 3 := by
  intro L hL
  obtain ⟨e⟩ := sylFamA_q8 hq h L hL
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem sylFamA_gen : omegaGen (sylFamA Ω A) = ⊤ := by
  have hY : (⨆ L ∈ {R' | R' ∈ RSet Ω ∧ R' ≤ Subgroup.centralizer (A : Set G)}, L) =
      rLayerSub Ω A := by
    unfold rLayerSub
    refine le_antisymm (iSup₂_le fun R' hR' => ?_) (iSup₂_le fun R' hR' => iSup_le fun hRC => ?_)
    · exact le_iSup₂_of_le R' hR'.1
        (le_iSup (fun _ : R' ≤ Subgroup.centralizer (A : Set G) => R') hR'.2)
    · exact le_iSup₂_of_le R' ⟨hR', hRC⟩ le_rfl
  have hX := omegaGen_restrictFamily_eq_top
    {R' | R' ∈ RSet Ω ∧ R' ≤ Subgroup.centralizer (A : Set G)} (rLayerSub Ω A) hY
  have hle : omegaGen (restrictFamily {R' | R' ∈ RSet Ω ∧ R' ≤ Subgroup.centralizer (A : Set G)}
      (rLayerSub Ω A)) ≤
      (omegaGen (sylFamA Ω A)).comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub Ω A))) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨R', ⟨hR', hRC⟩, hRX, rfl⟩ := hL
    refine (Subgroup.le_comap_map _ _).trans (Subgroup.comap_mono ?_)
    exact le_omegaGen (show secImage (rLayerSub Ω A) R' ∈ sylFamA Ω A from ⟨R', hR', hRC, rfl⟩)
  rw [hX, top_le_iff] at hle
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(rLayerSub Ω A)) x
  have hg : g ∈ (omegaGen (sylFamA Ω A)).comap
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub Ω A))) := by
    rw [hle]; exact Subgroup.mem_top g
  exact hg

end Fam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
