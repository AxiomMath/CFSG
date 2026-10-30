module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma45Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem szg_exists_outer {a c y : G}
    (hP : Sz32Struct P x J a c y) {U : Subgroup G} (hU : Sz32Plane P x a c y U) :
    ∃ u ∈ U, ∃ t ∈ u3T P x J, u * t * u⁻¹ ≠ t := by
  have hpres := hP.pres_P
  have hfacts := hP.facts
  have hex : ∃ u ∈ U, u ∉ sz32Z a c := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ sz32Z a c := hcon
    have h2 := hU.abs.inf_Z
    rw [inf_eq_left.mpr hle] at h2
    have h3 : Nat.card U = Nat.card (Subgroup.zpowers x) := by rw [h2]
    rw [hU.abs.card, Nat.card_zpowers, hpres.x_ord] at h3
    norm_num at h3
  obtain ⟨u, huU, huZ⟩ := hex
  refine ⟨u, huU, a, ?_, ?_⟩
  · rw [← hP.decomp.T_eq]
    exact Subgroup.mem_zpowers a
  · intro h
    have hcomm : a * u = u * a := (mul_inv_eq_iff_eq_mul.mp h).symm
    have hmem := hfacts.cent_le u (hU.abs.le_Om huU) huZ a hpres.a_mem hcomm
    have h5 : a ^ 5 = 1 := hfacts.Om_elem.2 a hmem
    have := orderOf_dvd_of_pow_eq_one h5
    rw [hpres.ord_a] at this
    norm_num at this

theorem szg_normalizer_J_le_M (hS : Setting G) (hU0 : FullCoreLocal G) {a c y : G}
    (hc : PointConfig IsSz32Type G 5 P M x J) (hP : Sz32Struct P x J a c y) :
    ∀ n : ↥J, (n : G) ∈ normalizer ((u3T P x J : Subgroup G) : Set G) → (n : G) ∈ M := by
  intro n hn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfacts := hP.facts
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  set E : Subgroup G := u3T P x J ⊔ Subgroup.zpowers x with hE
  have hEP : E ≤ (P : Subgroup G) := sup_le hTP (Subgroup.zpowers_le.mpr hxP)
  have hEp : IsPGroup 5 E := P.isPGroup'.to_le hEP
  have hZE : sz32Z a c ≤ E := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · have h5 : a ^ 5 ∈ u3T P x J := by
        rw [← hP.decomp.T_eq]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5
      exact (le_sup_left : u3T P x J ≤ E) h5
    · rw [← hfacts.x_eq]
      exact le_sup_right
  have hE2 : 2 ≤ CFSG.Open.pRank 5 E :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_pRank_of_elemAbelian_card (by norm_num) hZE
      hfacts.Z_elem hfacts.Z_card
  have hcomm : Commute (n : G) x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hJC n.2)
  have hzx : (Subgroup.zpowers x).map (MulAut.conj (n : G)) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    have : (MulAut.conj (n : G)) x = x := by
      rw [MulAut.conj_apply]
      exact mul_inv_eq_iff_eq_mul.mpr hcomm.eq
    simp [this]
  have hnE : (n : G) ∈ normalizer (E : Set G) := by
    have hn' := hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn' ⊢
    rw [hE, Subgroup.map_sup, hn', hzx]
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hEp (hEP.trans hPM) hE2 hnE

theorem sz32_lemma45_G (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) {U : Subgroup G} (hU : Sz32Plane P x a c y U) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hUS : U ≤ u3S P x := le_inf hU.le_P (hU.le_P.trans hP.le_cent)
  refine szg_lemma45_lift hS hD1 hSz'.lemma45 hSz'.maximal
    (fun A B _ _ e h => ⟨h.1, isoLie_of_mulEquiv e h.2⟩) hc (szg_normalizer_J_le_M hS hU0 hc hP) ?_
    hU.abs.elem hU.abs.card hUS hU.abs.mem (szg_exists_outer hP hU)
  intro s hs t ht
  rw [← hP.decomp.T_eq] at hs ht
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  exact (Commute.zpow_zpow_self a i j).eq

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
