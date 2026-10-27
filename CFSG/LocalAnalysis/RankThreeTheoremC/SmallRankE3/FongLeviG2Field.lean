module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.RankThree.PartOne.K133X.G2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcUntw
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.LemmaR
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti

section

set_option linter.unusedSectionVars false


theorem g2_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.G2 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)) : False := by
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥K (.G2 q) := ⟨hv, e⟩
  have hmodel := CFSG.RankThree.PartOne.K133X.chevalleyExceptionalModel_G2_of_isoLie hq2 hiso
  obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  haveI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  have hm2 : 2 ≤ q.exponent := by
    by_contra hlt
    have h3 : 3 ≤ 2 ^ q.exponent := hmodel.1.2.2.2
    have h1 : q.exponent = 1 := by have := hmodel.1.2.1; omega
    rw [h1] at h3
    omega
  obtain ⟨T₀, hT₀⟩ := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.exists_sylow_posUnipotent
    (τ := .G2) (K := F)
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport θ S.hpar T₀
  have hT₀' : (T₀ : Set ↥(adjointGroup Tag.G2 F)) =
      (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
        Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) :=
    congrArg (fun H : Subgroup ↥(adjointGroup Tag.G2 F) => (H : Set ↥(adjointGroup Tag.G2 F))) hT₀
  rw [hT₀'] at hN
  have hBP : borelGroup Tag.G2 F ≤ P.map (adjointGroup Tag.G2 F).subtype := by
    intro b hb
    have hbG : b ∈ adjointGroup Tag.G2 F := borelGroup_le_adjointGroup' hb
    have hbN : (⟨b, hbG⟩ : ↥(adjointGroup Tag.G2 F)) ∈
        normalizer (((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F) :
          Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq posUnipotent_le_adjointGroup]
      exact Subgroup.mem_subgroupOf.2
        (CFSG.SignalizerFunctorTheorem.NonLocalExc.borel_le_normalizer_posUnipotent hb)
    exact ⟨_, hN hbN, rfl⟩
  have hA : P.map (adjointGroup Tag.G2 F).subtype ≤ adjointGroup Tag.G2 F :=
    Subgroup.map_subtype_le P
  have hcl := (borel_overgroup_classification Tag.G2 F).1 _ hBP hA
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  have hJ : {i | weylElt Tag.G2 F i 1 ∈ P.map (adjointGroup Tag.G2 F).subtype} ≠ Set.univ := by
    intro hJ
    rw [hJ, (standard_parabolic_cells Tag.G2 F).2.2.2.2.2.1] at hcl
    apply hP
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL Tag.G2 F) ∈ P.map (adjointGroup Tag.G2 F).subtype := by
      rw [hcl]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.G2 F)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt θ] at h1
    exact h1
  refine g2_core hm2 hF S.hp S.hp5 hKr _ hJ (z := (z' : ModGL Tag.G2 F)) ?_ ?_
  · exact hcl.le ⟨z', hz'P, rfl⟩
  · rw [Subgroup.orderOf_coe]
    exact hzord

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
