module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinZ
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE186Quot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ComponentClassification

section Convert

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] def LieSystemData.toOmegaLie (D : LieSystemData p f X Φ) (hgen : omegaGen Φ = ⊤) :
    OmegaLie p f Φ where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom := D.hom
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate.trans hgen.symm
  fundamental := D.fundamental
  meets := D.meets

theorem omegaGen_oddQuotientFamily {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}
    (hgen : omegaGen Λ = ⊤) : omegaGen (oddQuotientFamily Λ) = ⊤ := by
  set mk := QuotientGroup.mk' (classicalInvolutionOddCore Y) with hmk
  have h1 : (omegaGen Λ).map mk ≤ omegaGen (oddQuotientFamily Λ) := by
    unfold omegaGen
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    exact le_iSup₂ (f := fun (M : Subgroup (Y ⧸ classicalInvolutionOddCore Y))
      (_ : M ∈ oddQuotientFamily Λ) => M) (L.map mk) ⟨L, hL, rfl⟩
  rw [hgen, Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h1
  exact top_le_iff.mp h1

end Convert


section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

abbrev secFam (Ω : Set (Subgroup G)) (c : G) :
    Set (Subgroup (↥(centralizingLayer (exactFamily Ω c) {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer (exactFamily Ω c) {c}))) :=
  oddQuotientFamily (restrictFamily (centralizingMembers (exactFamily Ω c) {c})
    (centralizingLayer (exactFamily Ω c) {c}))

theorem hypOmegaMod_secFam (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) : HypOmegaMod p f (secFam Ω c) := by
  have h1 : HypOmegaMod p f (exactPair Ω c) := hypOmegaMod_exactPair hp hq hΩ hc2
  have h2 : HypOmegaMod p f (restrictFamily (centralizingMembers (exactFamily Ω c) {c})
      (centralizingLayer (exactFamily Ω c) {c})) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl h1
  exact oddQuotHyp p f hp hq _ _ h2 (classicalInvolutionOddCore _) (OddCore.odd_card _)

theorem omegaGen_secFam (hs : SecData p f c (exactFamily Ω c)) : omegaGen (secFam Ω c) = ⊤ :=
  omegaGen_oddQuotientFamily (Λ := restrictFamily (centralizingMembers (exactFamily Ω c) {c})
    (centralizingLayer (exactFamily Ω c) {c})) hs.inClass.generated

theorem hypOmega_secFam (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) : HypOmega p f (secFam Ω c) := by
  have hmod := hypOmegaMod_secFam hp hq hΩ hc2
  exact hmod.toExact ((LieSystemData.toOmegaLie D (omegaGen_secFam hs)).exactMembers hp hq hmod)

theorem map_hom_eq_modOddIn (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card) {M : Subgroup G}
    (hM : M ∈ centMembers (exactFamily Ω c) c) {R : Subgroup (compModel D j).K}
    (hR : R.map (secComponentHom hs.normalizes D j) = modOdd c M) :
    R.map (D.hom j) = modOddIn (centralizingLayer (exactFamily Ω c) {c}) M := by
  apply Subgroup.map_injective (sectionQuotientHom_injective hs.normalizes)
  have h1 : (R.map (D.hom j)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D j) := Subgroup.map_map _ _ _
  exact h1.trans (hR.trans (map_sectionQuotientHom_modOddIn hs.normalizes hM).symm)

end Family


section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {M M' : Subgroup G}

theorem exactCore_ne_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hne : M' ≠ M) : exactCore c M' ≠ exactCore c M := by
  intro h
  obtain ⟨-, R, hR, hRc⟩ := (mem_tqMembers_iff_exists_sylow hp hq hΩ hc2).mp hM
  have hR' : IsSylow2In R (exactCore c M) :=
    (isSylow2In_exactCore_iff hΩ hc2 hM.1 hM.2).mpr ⟨hR, hRc⟩
  have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hM.1 hR)
  have hle : R ≤ M' := hR'.1.trans (by rw [← h]; exact exactCore_le_left c M')
  have := hΩ.card_le_two_of_le_inf hM.1 hM'.1 hne.symm hR.2.1 hR.1 hle
  omega

theorem secFam_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    {b : G} (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b)
    (hne : M' ≠ M) :
    ∃ hbY : b ∈ centralizingLayer (exactFamily Ω c) {c},
      modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M) ∈ secFam Ω c ∧
      modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M') ∈ secFam Ω c ∧
      modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M) ≠
        modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M') ∧
      IsUniqueInvolution (modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M))
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer (exactFamily Ω c) {c}))
          ⟨b, hbY⟩) ∧
      IsUniqueInvolution (modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c M'))
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer (exactFamily Ω c) {c}))
          ⟨b, hbY⟩) := by
  set Y := centralizingLayer (exactFamily Ω c) {c} with hY
  have hMc : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM, exactCore_le_centralizer c M⟩
  have hM'c : exactCore c M' ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hM', exactCore_le_centralizer c M'⟩
  have hMY : exactCore c M ≤ Y := le_centLayer hMc
  have hM'Y : exactCore c M' ≤ Y := le_centLayer hM'c
  have hb : b ∈ exactCore c M := mem_exactCore hMb hc2 hM.2
  have hbY : b ∈ Y := hMY hb
  have hU := TwinVertex.isUniqueInvolution_exactCore hp hq hMb hc2 hM.2
  have hU' := TwinVertex.isUniqueInvolution_exactCore hp hq hM'b hc2 hM'.2
  have hodd : ∀ K : Subgroup ↥Y, Odd (Nat.card ↥(classicalInvolutionOddCore ↥Y ⊓ K)) := fun K =>
    odd_natCard_inf (OddCore.odd_card ↥Y) K
  refine ⟨hbY, ⟨_, ⟨exactCore c M, hMc, hMY, rfl⟩, rfl⟩,
    ⟨_, ⟨exactCore c M', hM'c, hM'Y, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  ·
    have hΛ : HypOmegaMod p f (restrictFamily (centralizingMembers (exactFamily Ω c) {c})
        (centralizingLayer (exactFamily Ω c) {c})) :=
      hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
        (hypOmegaMod_exactPair hp hq hΩ hc2)
    have hK : (exactCore c M).subgroupOf Y ∈ restrictFamily (centralizingMembers
        (exactFamily Ω c) {c}) (centralizingLayer (exactFamily Ω c) {c}) :=
      ⟨exactCore c M, hMc, hMY, rfl⟩
    have hK' : (exactCore c M').subgroupOf Y ∈ restrictFamily (centralizingMembers
        (exactFamily Ω c) {c}) (centralizingLayer (exactFamily Ω c) {c}) :=
      ⟨exactCore c M', hM'c, hM'Y, rfl⟩
    have hne' : (exactCore c M').subgroupOf Y ≠ (exactCore c M).subgroupOf Y := fun h =>
      exactCore_ne_of_twin hp hq hΩ hc2 hM hM' hne
        (by
          have := congrArg (Subgroup.map Y.subtype) h
          rwa [Subgroup.map_subgroupOf_eq_of_le hM'Y, Subgroup.map_subgroupOf_eq_of_le hMY] at this)
    have htw : (exactCore c M').subgroupOf Y ∈ twinSet (restrictFamily (centralizingMembers
        (exactFamily Ω c) {c}) (centralizingLayer (exactFamily Ω c) {c}))
          ((exactCore c M).subgroupOf Y) :=
      ⟨hK', ⟨b, hbY⟩, isUniqueInvolution_subgroupOf hU hMY, isUniqueInvolution_subgroupOf hU' hM'Y⟩
    exact fun h => map_ne_of_twin hp hq hΛ (OddCore.odd_card ↥Y) hK htw hne' h.symm
  · exact isUniqueInvolution_map_mk_of_odd (hodd _) (isUniqueInvolution_subgroupOf hU hMY)
  · exact isUniqueInvolution_map_mk_of_odd (hodd _) (isUniqueInvolution_subgroupOf hU' hM'Y)

end Twins

end CFSG.ClassicalInvolution.Asc77
