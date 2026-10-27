module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits (reeG2_valid
  nonempty_reeGamma_equiv_catalog isChevSimple_commutator_reeGamma fixSubgroup_eq_fixSub)

section G2

set_option linter.unusedSectionVars false


theorem nonempty_commutator_reeGamma_G2_cat (b : ℕ) (k : Type) [Field k] [Finite k]
    [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty (↥(commutator (ReeTag.G2.reeGamma k b)) ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨-, -, -, ⟨e⟩, -, -⟩ :=
      CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure hk
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q8 : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
    have hv8 : (TauCeti.LieTypeIndex.A 1 q8).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [TauCeti.PrimePower.card_def, q8]
      norm_num
    exact ⟨⟨.A 1 q8, hv8⟩,
      ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q8 hv8).symm⟩⟩
  · obtain ⟨htop, -, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb k hk
    have hv := reeG2_valid hb
    obtain ⟨φ⟩ := nonempty_reeGamma_equiv_catalog b hv k hk
    exact ⟨⟨.reeG2 b, hv⟩, ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans φ⟩⟩

theorem srtOut_reeGamma_G2_outer {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut (ReeTag.G2.reeGamma K a)} (hβ : β ^ p = 1)
    (hin : β ∉ (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)).range) : SRTOut 3 β := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, δ, σ, hσord, hδ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2 β hβ
      hin
  obtain ⟨b, -, hbcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hp hp2 hσord
  haveI := hchar
  refine SRTOut.of_conj δ ?_
  rw [hδ]
  let e : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (MulEquiv.subgroupCongr (fixSubgroup_eq_fixSub _)).trans eC
  obtain ⟨hs, hnc, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b
      (fixSubfield σ) hbcard
  obtain ⟨idx, ⟨hcat⟩⟩ := nonempty_commutator_reeGamma_G2_cat b (fixSubfield σ) hbcard
  haveI := hs
  haveI : Finite ↥(commutator (ReeTag.G2.reeGamma (fixSubfield σ) b)) := inferInstance
  exact srtOut_of_fixed_equiv_derived _ e hs hnc (isChevSimple_commutator_reeGamma b _ hbcard)
    fun hb => isEmpty_quot_alternating_six_of_equiv_cat hb hnc idx ⟨hcat⟩

theorem srtOut_reeGamma_G2 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {β : MulAut (ReeTag.G2.reeGamma K a)} (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) : SRTOut 3 β := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hin : β ∈
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range
  · obtain ⟨-, hsimple, hnc⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha K hK
    haveI := hsimple
    obtain ⟨x, rfl, hxp, hx1⟩ :=
      exists_eq_conj_of_mem_range (b3Lie_center_eq_bot hnc) hin hβ hβ1
    refine srtOut_of_isSolvable 3 _ ?_
    rw [fixSubgroup_conj]
    exact isSolvable_centralizer_reeGamma_G2 ha K hK hp hp2 hp3 (orderOf_eq_prime hxp hx1)
  · exact srtOut_reeGamma_G2_outer ha hK hp hp2 hβ hin

theorem srtOut_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {S : Type} [Group S]
    [Finite S] (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    SRTOut 3 β := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, he⟩)
  refine SRTOut.of_congr e ?_
  refine srtOut_reeGamma_G2 ha hK hp hp2 hp3 ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · intro h
    exact hβ1 ((MulAut.congr e).map_eq_one_iff.mp h)

theorem srtOut_reeG2_outer (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {S : Type}
    [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1)
    (hout : ∀ t : S, MulAut.conj t ≠ β) : SRTOut 3 β := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, he⟩)
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  refine SRTOut.of_congr e ?_
  refine srtOut_reeGamma_G2_outer ha hK hp hp2 (by rw [← map_pow, hβ, map_one]) ?_
  rintro ⟨t, ht⟩
  apply hout (e.symm t)
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  exact ht

end G2

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
