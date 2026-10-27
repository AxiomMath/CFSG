module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.GLThreeOf
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists MatrixGroups

private theorem center_eq_bot_of_mulEquiv {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hY : CFSG.IsQuasisimple Y) (e : Y ≃* S) : Subgroup.center Y = ⊥ := by
  have : IsSimpleGroup Y := e.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hY.2.2
    have h1 : ∀ c : Y ⧸ Subgroup.center Y, c = 1 := fun c => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      exact (QuotientGroup.eq_one_iff x).mpr (h ▸ Subgroup.mem_top x)
    exact hab (by rw [h1 a, h1 b])

private theorem nonempty_quot_center_equiv {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hY : CFSG.IsQuasisimple Y) (e : Y ≃* S) : Nonempty (Y ⧸ Subgroup.center Y ≃* S) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_mulEquiv hY e)).trans
    (QuotientGroup.quotientBot.trans e)⟩

private theorem isLowDimSimpleSection_statedSL (q : ℕ) [Fact q.Prime] :
    IsLowDimSimpleSection q
      (↥(CFSG.Open.StatedSL 3 (ZMod q)) ⧸ Subgroup.center ↥(CFSG.Open.StatedSL 3 (ZMod q))) :=
  Or.inr (Or.inl ⟨QuotientGroup.congr _ _
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod q)).symm
    (Subgroup.map_center_eq _)⟩)

private theorem isSimpleGroup_GL_three_two : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  have : IsSimpleGroup PSL(2, ZMod 7) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  exact e.isSimpleGroup

private theorem isLowDimSimpleSection_of_five_le (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {Y : Subgroup (GL (Fin 3) (ZMod q))}
    (hY : CFSG.IsQuasisimple Y) (hirr : IsIrreducibleOn Y) :
    IsLowDimSimpleSection q (↥Y ⧸ Subgroup.center ↥Y) := by
  have := hY.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  obtain ⟨H, hHY, hn, hHirr, hcase⟩ := hB q (by omega) (isIrreducibleOn_iff.mp hirr)
  obtain rfl := glThree_eq_of_normal_irreducible hY hHY hn (isIrreducibleOn_iff.mpr hHirr)
  rcases hcase with rfl | ⟨M, hMt, hdet, rfl⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, -, hA6, -⟩ | ⟨hcyc, -⟩ |
      ⟨h27, -⟩ | ⟨-, hmon⟩
  · exact isLowDimSimpleSection_statedSL q
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hq5 hMt hdet
    have : IsSimpleGroup PSL(2, ZMod q) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
    exact Or.inl (nonempty_quot_center_equiv hY e)
  · have := alternatingGroup.isSimpleGroup_five
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (nonempty_quot_center_equiv hY e)))))
  · have := isSimpleGroup_GL_three_two
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (nonempty_quot_center_equiv hY e)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA6)))))
  · exact absurd (IsCyclic.isMulCommutative (α := H)) (Group.IsPerfect.not_isMulCommutative H)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact absurd (IsPGroup.of_card (p := 3) (n := 3) h27).isNilpotent
      (Group.IsPerfect.not_isNilpotent _)
  · exact absurd hmon not_isTransitiveMonomial_of_perfect

theorem gLThreeQuasisimpleLowDim_of (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (h33 : ∀ G : Subgroup (GL (Fin 3) (ZMod 3)), Group.IsPerfect G → G ≠ ⊥ → G = CFSG.Open.StatedSL
        3 (ZMod 3)) : GLThreeQuasisimpleLowDim := by
  intro q _ hq2 Y hY hirr
  have hq : q.Prime := Fact.out
  rcases (by have := hq.two_le; have := hq.eq_one_or_self_of_dvd 2; omega :
      q = 3 ∨ 5 ≤ q) with rfl | hq5
  · have := hY.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hY
    obtain rfl := h33 Y hY.1 ((Subgroup.nontrivial_iff_ne_bot Y).mp inferInstance)
    exact isLowDimSimpleSection_statedSL 3
  · exact isLowDimSimpleSection_of_five_le hB hq5 hY hirr

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
