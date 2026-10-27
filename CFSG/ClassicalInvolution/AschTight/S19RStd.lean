module

public import CFSG.ClassicalInvolution.AschTight.T6ASetup
public import CFSG.ClassicalInvolution.Asc77.WP2Thm6

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem not_dConnected_of_setup194 [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (h : T6A.Setup194 p f K z) : ¬ DConnected (CoreAssembly.conjClass K) := by
  intro hc
  have hall : ∀ J ∈ CoreAssembly.conjClass K, J = K := by
    intro J hJ
    rcases Relation.ReflTransGen.cases_head (hc K (CoreAssembly.mem_conjClass_self K) J hJ) with
      h1 | ⟨c, ⟨hc1, hc2⟩, -⟩
    · exact h1.symm
    · exact absurd hc2 (h.edgeless K (CoreAssembly.mem_conjClass_self K) c hc1)
  have hz := h.isUniqueInvolution
  have hKtop : K = ⊤ := by
    have hgen := gen_conjClass K hz.mem hz.ne_one
    exact eq_top_iff.mpr (hgen ▸ iSup₂_le fun J hJ => (hall J hJ).le)
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← h.normEq, hKtop, Subgroup.mem_normalizer_iff]
      intro k
      simp
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have htop : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
    · rw [h1, Subgroup.mem_bot] at hzc
      exact absurd hzc hz.ne_one
    · exact h1
  obtain ⟨x, y, hxy⟩ := h.nonabelian
  have hx : x ∈ Subgroup.center G := htop ▸ Subgroup.mem_top x
  exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem three_le_twoRank_of_not_fourGenerated (h : ¬ TwoSubgroupsFourGenerated G) :
    3 ≤ twoRank G := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨E, -, -, hE, hE8⟩ := exists_normal_elemAbelian_eight_of_not_fourGenerated h S
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G E hE 3 (by rw [hE8]; norm_num)

theorem dBranchD_of_std6 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) : DBranchD p f K z := by
  have h := T6A.setup194_of_stand hstd.stand hstd.edgeless hstd.hz
  have hn : ¬ TwoSubgroupsFourGenerated G := fun h4 => hstd.cex (Or.inr h4)
  exact ⟨h.nonabelian, h.odd, h.five, hstd.stand.below f h.five, h.member,
    three_le_twoRank_of_not_fourGenerated hn, hn, not_dConnected_of_setup194 h⟩

theorem tightStd_of_std6 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) : TightStd p f K z :=
  have h := T6A.setup194_of_stand hstd.stand hstd.edgeless hstd.hz
  ⟨dBranchD_of_std6 hstd, h.normEq, h.edgeless⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19R
