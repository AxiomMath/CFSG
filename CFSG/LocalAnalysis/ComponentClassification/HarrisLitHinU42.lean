module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinClsEven
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

theorem statedClassicalModel_PSU_four_two_of_PSp_two_three {G : Type} [Group G]
    (h : Assembly.LowTwoRank.StatedClassicalModel G .PSp 2 3 1) :
    Assembly.LowTwoRank.StatedClassicalModel G .PSU 4 2 1 := by
  set U := Assembly.LowTwoRank.StatedProj
    (Assembly.LowTwoRank.StatedSU 4 (2 ^ 1) Blueprint.Fischer.K)
  have hU : Assembly.LowTwoRank.StatedClassicalModel U .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, Blueprint.Fischer.K, inferInstance,
      inferInstance, Fischer.Classification.Recognition.card_K, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    (GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hU)
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := hU
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem hinConcl_psp_four_three (hnab : ∃ a b : Y, a * b ≠ b * a)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSp 2 3 1) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ :=
  hinConcl_psu_even hnab (statedClassicalModel_PSU_four_two_of_PSp_two_three hY) hp hp2 hm h16
    hτ hL

end CFSG.ComponentClassification.HarrisLit.Hin
