module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigC1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2C264
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
open CFSG.Blueprint

section Gen

variable {G : Type} [Group G] [Finite G]

theorem map_pCore_le_pCore {X : Subgroup G} (hX : X.Normal) :
    (pCore 2 ↥X).map X.subtype ≤ pCore 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (pCore 2 ↥X).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  have hn := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := X) (pCore 2 ↥X)
  have hN : ((pCore 2 ↥X).map X.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hX]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp (hn hg) x).mp hx
  exact CFSG.LieType.BorelTits.le_pCore 2 hN (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

private theorem exists_mem_USet_le_gen {Q : Type} [Group Q] [Finite Q] {Ω : Set (Subgroup Q)}
    (hΩ : HypOmegaGen Ω) {J : Subgroup Q} (hJ : J ∈ Ω) :
    ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ
    (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Q)) bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem exists_core_le_pCore (hr : 4 ≤ r) (h4 : Thm4RBelow r n)
    (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t) :
    ∃ U₀ : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)),
      U₀ ≤ secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ∧
      2 < Nat.card ↥U₀ ∧
      U₀ ≤ pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
  obtain ⟨W, hW⟩ := exists_std8 hs
  set Ω : Set (Subgroup Y) := CoreAssembly.conjClass (tightCore R) with hΩ
  set Kb : Subgroup (SecQuot Ω (t * u)) := secImg Ω (t * u) (tightCore R) with hKb
  set X : Subgroup (SecQuot Ω (t * u)) := secOrb Ω (tightCore R) (t * u) with hX
  set Φ : Set (Subgroup ↥X) := restrictFamily (TL4.secFam Ω (t * u)) X with hΦ
  have hD := thmDHyp_secOrbR (by omega : 2 ≤ r) h4 hW hO2
  have hnorm : ∀ U ∈ USet Φ, ∀ U' ∈ USet Φ, U' ≤ Subgroup.normalizer (U : Set ↥X) :=
    fun U hU U' hU' =>
      le_normalizer_of_four_le hr hD.hyp hD.two hD.card hD.aEmpty hD.odd hD.inO2 hU hU'
  have hpc : (⨆ U ∈ USet Φ, U : Subgroup ↥X) ≤ pCore 2 ↥X := iSup_uSet_le_pCore hD.hyp hnorm
  have hXnorm : X.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply eq_top_iff.mpr
    intro g _
    rw [mem_normalizer_iff_conjSub_eq]
    exact Vtx.conjSub_orbGrp (by rw [TL4.omegaGen_secFam]; exact Subgroup.mem_top g)
  have hKbΦ : Kb ∈ TL4.secFam Ω (t * u) := by
    rw [hKb]; exact secImg_mem hW.xMem_K
  have hKbX : Kb ≤ X := by
    rw [hKb, hX]; exact Vtx.le_orbGrp _
  have hKsubΦ : Kb.subgroupOf X ∈ Φ := ⟨Kb, hKbΦ, hKbX, rfl⟩
  obtain ⟨U, hU, hUK⟩ := exists_mem_USet_le_gen hD.hyp hKsubΦ
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hD.hyp hU
  refine ⟨U.map X.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hUK).trans (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hKbX))
  · calc 2 < Nat.card ↥U := lt_of_lt_of_le (by norm_num) hU4
      _ = Nat.card ↥(U.map X.subtype) :=
        (Subgroup.card_map_of_injective X.subtype_injective).symm
  · have hUle : U ≤ ⨆ U ∈ USet Φ, U :=
      le_iSup₂ (f := fun U (_ : U ∈ USet Φ) => U) U hU
    exact (Subgroup.map_mono (hUle.trans hpc)).trans (map_pCore_le_pCore hXnorm)

theorem exists_sylow_image (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ∃ P₂ : Subgroup ↥(layerY (CoreAssembly.conjClass (tightCore R)) (t * u)),
      IsPGroup 2 ↥P₂ ∧
      P₂.map (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)).subtype ≤ (P : Subgroup Y) ∧
      pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ≤
        P₂.map (QuotientGroup.mk'
          (classicalInvolutionOddCore
            ↥(layerY (CoreAssembly.conjClass (tightCore R)) (t * u)))) := by
  set Ω : Set (Subgroup Y) := CoreAssembly.conjClass (tightCore R) with hΩ
  set X : Subgroup Y := layerY Ω (t * u) with hX
  have hcl : ConjInvariant Ω := hs.large.datum.hypOmegaGen.conjInvariant
  have hPN : (P : Subgroup Y) ≤ Subgroup.normalizer (X : Set Y) := by
    intro y hy
    rw [hX]
    exact mem_normalizer_layerY hcl
      (Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_tu hy))
  have hPsylY : IsSylow2In (P : Subgroup Y) ⊤ := T8.isSylow2In_of_sylow_le P le_top
  have hPsylM : IsSylow2In (P : Subgroup Y) (Subgroup.normalizer (X : Set Y)) :=
    ⟨hPN, hPsylY.2.1, fun V' _ hV'2 hle => hPsylY.2.2 V' le_top hV'2 hle⟩
  have hP2syl : IsSylow2In ((P : Subgroup Y) ⊓ X) X :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hPsylM Subgroup.le_normalizer le_rfl
  set P₂ : Subgroup ↥X := ((P : Subgroup Y) ⊓ X).subgroupOf X with hP₂
  have hP₂2 : IsPGroup 2 ↥P₂ := hP2syl.2.1.comap_subtype
  have hP₂sylTop : IsSylow2In P₂ ⊤ := by
    have h := hP2syl.subgroupOf (Y := X) le_rfl
    rw [Subgroup.subgroupOf_self] at h
    rwa [hP₂]
  have hP₂map : P₂.map X.subtype = (P : Subgroup Y) ⊓ X := by
    rw [hP₂]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hP₂leP : P₂.map X.subtype ≤ (P : Subgroup Y) := hP₂map.le.trans inf_le_left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  set Q₂ : Subgroup (SecQuot Ω (t * u)) :=
    P₂.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) with hQ₂
  have hQ₂syl : IsSylow2In Q₂ ⊤ := by
    have h := isSylow2In_map_mk hodd hP₂sylTop
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    rwa [hQ₂]
  have hpZ2 : IsPGroup 2 ↥(pCore 2 (SecQuot Ω (t * u))) :=
    CFSG.LieType.BorelTits.pCore_isPGroup 2
  haveI : (pCore 2 (SecQuot Ω (t * u))).Normal :=
    CFSG.LieType.BorelTits.pCore_normal 2
  have hsup : pCore 2 (SecQuot Ω (t * u)) ⊔ Q₂ = Q₂ :=
    hQ₂syl.2.2 _ le_top (hpZ2.to_sup_of_normal_left hQ₂syl.2.1) le_sup_right
  exact ⟨P₂, hP₂2, hP₂leP, le_sup_left.trans_eq hsup⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264
