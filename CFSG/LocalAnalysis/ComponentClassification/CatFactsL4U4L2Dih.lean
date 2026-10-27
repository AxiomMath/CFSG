module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Dih

open CFSG Subgroup

theorem dihedral_of_lieModel_psl_two : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ),
    p.Prime → p ≠ 2 → 1 ≤ f → Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y,
      8 ≤ Nat.card T → ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(T : Subgroup Y) ≃* DihedralGroup (2 ^ m)) := by
  intro Y _ _ p f hp hp2 hf hL T hT
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := FooteLit.statedClassicalModel_of_lieModel_psl_two hL
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩
  have hD := OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv
    (e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
    (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd)
  obtain ⟨m, hm, ⟨φ⟩⟩ := hD T
  refine ⟨m, ?_, ⟨φ⟩⟩
  have hcard : Nat.card T = 2 * 2 ^ m := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  by_contra hlt
  push Not at hlt
  interval_cases m
  · simp at hcard
    omega

end L2Dih

end CFSG.ComponentClassification.CatFactsL4U4
