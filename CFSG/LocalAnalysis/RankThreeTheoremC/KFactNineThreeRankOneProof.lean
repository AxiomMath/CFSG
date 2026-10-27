module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
import CFSG.Quasithin.Background.B682Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111KappaMoves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.AGLEmbedding CFSG.QuasiDihedralFusion

namespace KFRankOne

theorem finite_of_involves {A K : Type*} [Group A] [Finite A] [Group K] (h : Involves A K) :
    Finite K := by
  obtain ⟨U, φ, hφ⟩ := h
  exact Finite.of_surjective φ hφ

theorem nineThreeListGroup_of_mulEquiv {p : ℕ} {X Z : Type*} [Group X] [Group Z] (e : Z ≃* X)
    (h : NineThreeListGroup p X) : NineThreeListGroup p Z := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans f⟩⟩

theorem exists_cyclic_sylow_of_involves {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type}
    [Group Y] [Finite Y] {K : Subgroup Y} (hr : CFSG.Open.pRank p K ≤ 1) {A : Type} [Group A]
    (hI : Involves K A) : ∃ T : Sylow p A, IsCyclic (T : Subgroup A) := by
  obtain ⟨U, φ, hφ⟩ := hI
  obtain ⟨P⟩ : Nonempty (Sylow p U) := inferInstance
  refine ⟨P.mapSurjective hφ, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hS : IsCyclic (((P : Subgroup U).map U.subtype).map K.subtype) :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one hp2 (Subgroup.map_subtype_le _)
      ((P.isPGroup'.map U.subtype).map K.subtype) hr
  rw [Subgroup.map_map] at hS
  have hP : IsCyclic (P : Subgroup U) :=
    (MulEquiv.isCyclic ((P : Subgroup U).equivMapOfInjective _
      (K.subtype_injective.comp U.subtype_injective))).mpr hS
  exact isCyclic_of_surjective (φ.subgroupMap P) (φ.subgroupMap_surjective P)

theorem card_eq_of_isCaseTwoGroup {p : ℕ} {X Z : Type} [Group X] [Group Z]
    (hX : IsCaseTwoGroup p X) (hZ : IsCaseTwoGroup p Z) : Nat.card X = Nat.card Z := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_isCaseTwoGroup hX hZ
  exact Nat.card_congr e.toEquiv

end KFRankOne

theorem kFactNineThreeRankOne_of (hKL : KFactNineThreeListRankOne) : KFactNineThreeRankOne := by
  intro p Y _ _ K A _ hK hA hr hI
  have hcase : IsCaseTwoGroup p K := hKL p Y K hK hr
  have hp : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd, -⟩ := hcase
    rcases hd with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  haveI := KFRankOne.finite_of_involves hI
  obtain ⟨T, hT⟩ := KFRankOne.exists_cyclic_sylow_of_involves (by omega) hr hI
  have hA' : NineThreeListGroup p ↥(⊤ : Subgroup A) :=
    KFRankOne.nineThreeListGroup_of_mulEquiv Subgroup.topEquiv hA
  have hcaseA : IsCaseTwoGroup p ↥(⊤ : Subgroup A) :=
    hKL p A ⊤ hA' (InnerQ.pRank_top_le_one_of_isCyclic T hT)
  have := KFRankOne.card_eq_of_isCaseTwoGroup hcaseA hcase
  rwa [Subgroup.card_top] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
