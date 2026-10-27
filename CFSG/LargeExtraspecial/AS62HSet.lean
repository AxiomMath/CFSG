module

public import CFSG.LargeExtraspecial.AS62TI
public import CFSG.LargeExtraspecial.AS62Beta2
public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS35DSixFour
public import CFSG.LargeExtraspecial.AS35DSixThreeE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_isHSet (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) :
    ∃ H : Subgroup G, S.IsHSet H := by
  obtain ⟨g₀, hg₀M, hg₀⟩ := exists_inf_Qa_ne_bot h
  obtain ⟨c⟩ := S.exists_sixThreeCtx h.hw.ge h.hW h.hO hg₀M hg₀
  rcases c.twoTwo h22 with hS | hA
  · by_cases hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u
    · exact (c.false_of_inf_le_two h.hw hS hQQ).elim
    · push Not at hQQ
      obtain ⟨w, hw, hw1, hwu⟩ := hQQ
      exact ⟨_, c.isHSet_of_not_inf_le hS hw hw1 hwu⟩
  · exact (c.false_of_aFive hA).elim

theorem sixFourConcl (h22 : S14.AschbacherTwoTwoStmt)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) : S.SixFourConcl := by
  intro H hH
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH.1.2.2
  exact ⟨(S.sixFour h22 hW hH hgH hgM).1,
    fun g' hg'H hg'M => (S.sixFour h22 hW hH hg'H hg'M).2⟩

theorem exists_mem_DSet (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) :
    ∃ t ∈ S.DSet, t ∈ S.M := by
  have hS := sixFourConcl h22 h.hW
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS (exists_isHSet h22 h)
  exact ⟨t, ht, S.mem_M_of_mem_ESet hS ht.1⟩

end AS62

end CFSG.LargeExtraspecial
