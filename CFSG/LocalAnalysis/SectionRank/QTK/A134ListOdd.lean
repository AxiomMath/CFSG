module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Quasithin.Background.A3Structure38Facts
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListAlt
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.Quasithin.Background.A3FactsA134
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)

variable {S : Type} [Group S] [Finite S]

theorem oddLocalWitness_psl_three_odd {p : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel S .PSL 3 p 1) : OddLocalWitness S := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp le_rfl hK
  refine ⟨p, hp, hp2, CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2 (Or.inl hm), ?_⟩
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm) hp]
  exact CFSG.RankThree.PartOne.Census3.le_localRank_PSL_three hp2 hK

theorem oddLocalWitness_psu_three_odd {p : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel S .PSU 3 p 1) : OddLocalWitness S := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  refine ⟨p, hp, hp2, CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2 (Or.inr hm), ?_⟩
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (e.trans (unitaryPSUEquiv hU (by norm_num)).symm) hp]
  have := CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hU hp2 (n := 3) (r := 1) le_rfl
    (by norm_num)
  simpa using this

theorem oddLocalWitness_psl_two_nine (hm : StatedClassicalModel S .PSL 2 3 2) :
    OddLocalWitness S := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.alternating_six_of_model_nine hm
  exact OddLocalWitness.of_mulEquiv e (oddLocalWitness_alternating (Or.inl rfl))

theorem a134Types_or_oddLocalWitness_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel S .PSL 2 p f) ∨
      StatedClassicalModel S .PSL 3 p 1 ∨ StatedClassicalModel S .PSU 3 p 1) :
    CFSG.Quasithin.A134Types S ∨ OddLocalWitness S := by
  rcases h with ⟨f, hf, hm⟩ | hm | hm
  · by_cases hp3 : 3 < p
    · rcases hf with rfl | rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨p, 1, hp, hp3, le_rfl, by norm_num, hm⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨p, 2, hp, hp3, by norm_num, le_rfl, hm⟩)))
    · have hp3' : p = 3 := by have := hp.two_le; omega
      subst hp3'
      rcases hf with rfl | rfl
      · exact absurd (by norm_num : ((2 : ℕ), 3 ^ 1) = (2, 3)) hm.1.2.2.2.2
      · exact Or.inr (oddLocalWitness_psl_two_nine hm)
  · exact Or.inr (oddLocalWitness_psl_three_odd hp2 hm)
  · exact Or.inr (oddLocalWitness_psu_three_odd hp2 hm)

end CFSG.SectionRank.QTK
