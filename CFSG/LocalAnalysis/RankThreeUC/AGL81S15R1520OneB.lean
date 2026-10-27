module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneA
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique CFSG.Open Subgroup

theorem charTwo_top_of_sub {X : Type*} [Group X] {D : Subgroup X} (h : CharTwo D) :
    CharTwo (⊤ : Subgroup ↥D) := by
  intro x hx
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2]
  have hxc : x ∈ Subgroup.centralizer (CFSG.pCore 2 ↥D : Set ↥D) := by
    have := hx.2
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2] at this
  have hxD : (x : X) ∈ D ⊓ Subgroup.centralizer (pCoreOf 2 D : Set X) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have hg' : g ∈ (CFSG.pCore 2 ↥D).map D.subtype := hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg'
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxc y hy)
  have hxm : (x : X) ∈ (CFSG.pCore 2 ↥D).map D.subtype := h hxD
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxm
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

theorem isSylowTwoOf_top_of_sub {X : Type*} [Group X] {D T : Subgroup X} (hT : IsSylowTwoOf T D) :
    IsSylowTwoOf (T.subgroupOf D) (⊤ : Subgroup ↥D) := by
  obtain ⟨hTD, hp, hidx⟩ := hT
  refine ⟨le_top, hp.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm, ?_⟩
  rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]

theorem k520_2_of_isKGroup_sub
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) {D T : Subgroup X} (h3 : ¬ 3 ∣ Nat.card D) (hc : CharTwo D)
    (hT : IsSylowTwoOf T D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 1 < CFSG.Open.pRank p D) :
    ∃ T₀ : Subgroup X, T₀ ≠ ⊥ ∧ T₀ ≤ T ∧ (T₀.subgroupOf T).Characteristic ∧
      1 < CFSG.Open.pRank p (normalizer (T₀ : Set X)) := by
  have hrk' : 1 < CFSG.Open.pRank p (⊤ : Subgroup ↥D) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  obtain ⟨T₀, hne, hle, hchar, hN⟩ :=
    k520_2_of_isKGroup hSz (hK.subgroup D) h3 (charTwo_top_of_sub hc) (isSylowTwoOf_top_of_sub hT)
      hp hp2 hrk'
  obtain ⟨hTle, hTchar⟩ := map_subtype_characteristic hT.1 hle hchar
  refine ⟨T₀.map D.subtype, ?_, hTle, hTchar, ?_⟩
  · intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective T₀ D.subtype_injective).mp h)
  · have h2 := CFSG.SectionRank.pRank_le_map hp.one_lt D.subtype D.subtype_injective
      (normalizer (T₀ : Set ↥D))
    have h3' := CFSG.SectionRank.pRank_mono hp.one_lt
      (Subgroup.le_normalizer_map (H := T₀) D.subtype)
    exact lt_of_lt_of_le hN (h2.trans h3')

end CFSG.LocalAnalysis.RankThreeUC.S15
