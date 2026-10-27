module

public import CFSG.GH74.Conclusion
public import CFSG.GH74.Bender.Unitary
public import CFSG.GH74.Bender.Suzuki
public import CFSG.Milestones.SE_simple_strong_embedding_models
import CFSG.Assembly.Disconnected
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.GH74

open Blueprint Assembly.LowTwoRank

theorem twoRank_eq_of_mulEquiv_psl2Model {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.PSL2Model n) : CFSG.Open.twoRank G = n := by
  have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv G e.toEquiv
  rw [twoRank_eq_of_mulEquiv e]
  exact CFSG.ShultStronglyClosedTI.LinearModel.twoRank_eq (K := GaloisField 2 n)
    (GaloisField.card 2 n (by omega))

theorem lieModel_PSL_two_two_of_mulEquiv_psl2Model {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.PSL2Model n) : LieModel G .PSL 2 2 n :=
  Or.inl ⟨by decide, statedClassicalModel_psl_two_of_mulEquiv G 2 n
    ((by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hn)) e⟩

theorem gh74Conclusion_of_isBenderGroup {G : Type} [Group G] [Finite G]
    (hB : CFSG.BenderSuzuki.IsBenderGroup G) (hrank : 3 ≤ CFSG.Open.twoRank G) (hgen : Gen4 G) :
    GH74Conclusion G := by
  have h4 : CFSG.Open.twoRank G ≤ 4 := hgen.twoRank_le
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have hrk := twoRank_eq_of_mulEquiv_psl2Model (by omega) e
    have hn34 : n = 3 ∨ n = 4 := by omega
    rcases hn34 with rfl | rfl
    · exact GH74Conclusion.of_eight
        (Or.inl (lieModel_PSL_two_two_of_mulEquiv_psl2Model le_rfl e))
    · exact GH74Conclusion.of_eight
        (Or.inr (Or.inl (lieModel_PSL_two_two_of_mulEquiv_psl2Model (by norm_num) e)))
  · have e' : G ≃* CFSG.Open.Sz n := e.trans (MulEquiv.subgroupCongr (Bender.szModel_eq_sz n))
    have : Finite (CFSG.Open.Sz n) := Finite.of_equiv G e'.toEquiv
    have h1 := Bender.le_twoRank_sz hn
    have h2 : CFSG.Open.twoRank G = CFSG.Open.twoRank (CFSG.Open.Sz n) :=
      twoRank_eq_of_mulEquiv e'
    have hn1 : n = 1 := by omega
    subst hn1
    exact GH74Conclusion.of_eight
      (Or.inr (Or.inr (Or.inr (Bender.lieModel_twistedB2_of_mulEquiv_sz_one e'))))
  · exact (Bender.false_of_mulEquiv_psu3Model hn e hrank hgen).elim

theorem isBenderGroup_of_fusionIsBenderGroup {X : Type*} [Group X]
    (h : CFSG.Open.fusionIsBenderGroup X) : CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
        CFSG.Models.benderPSU3Model_eq_psu3 f
    exact .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  · exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr (Bender.szModel_eq_sz a).symm))

theorem gh74Conclusion_of_fusionIsBenderGroup {G : Type} [Group G] [Finite G]
    (hB : CFSG.Open.fusionIsBenderGroup G) (hrank : 3 ≤ CFSG.Open.twoRank G) (hgen : Gen4 G) :
    GH74Conclusion G :=
  gh74Conclusion_of_isBenderGroup (isBenderGroup_of_fusionIsBenderGroup hB) hrank hgen

theorem gh74Conclusion_of_stronglyEmbedded
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (M : Subgroup G) (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    (hrank : 3 ≤ CFSG.Open.twoRank G) (hgen : Gen4 G) : GH74Conclusion G :=
  gh74Conclusion_of_isBenderGroup (CFSG.Milestones.bender_suzuki M hM) hrank hgen

theorem even_card_of_three_le_twoRank {G : Type*} [Group G] [Finite G]
    (hrank : 3 ≤ CFSG.Open.twoRank G) : Even (Nat.card G) := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 2) Nat.one_lt_two (⊤ : Subgroup G)
  have h3 : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := hrank
  have h1 : 2 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 2 (by omega)
  exact even_iff_two_dvd.mpr (h1.trans (Subgroup.card_subgroup_dvd_card E))

theorem gh74Conclusion_of_disconnected
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hdisc : ¬ (CFSG.Assembly.involutionGraph G).Preconnected)
    (hrank : 3 ≤ CFSG.Open.twoRank G) (hgen : Gen4 G) : GH74Conclusion G := by
  have heven := even_card_of_three_le_twoRank hrank
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬ (CFSG.Assembly.involutionGraph G).Reachable u v := by
    simpa [SimpleGraph.Preconnected] using hdisc
  have hne : (CFSG.Assembly.involutionGraph G).connectedComponentMk u ≠
      (CFSG.Assembly.involutionGraph G).connectedComponentMk v := by
    rwa [Ne, SimpleGraph.ConnectedComponent.eq]
  obtain ⟨hMne, hMeven, hModd⟩ :=
    CFSG.Assembly.Disconnected.component_stabilizer_strongly_embedded G heven ⟨_, _, hne⟩
      ((CFSG.Assembly.involutionGraph G).connectedComponentMk u)
  exact gh74Conclusion_of_stronglyEmbedded _
    ⟨hMne, hMeven, fun g hg => by simpa using hModd g⁻¹ (by simpa using hg)⟩ hrank hgen

end CFSG.GH74
