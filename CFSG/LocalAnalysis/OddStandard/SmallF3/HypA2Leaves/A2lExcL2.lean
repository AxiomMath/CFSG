module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwoDatum

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem a2l_two_le_of_psl_two_three {S : Type} [Group S] {e : ℕ} (he : LieModel S .PSL 2 3 e) :
    2 ≤ e := by
  obtain ⟨-, hf, -, -, h3⟩ := he.admissible
  by_contra hlt
  obtain rfl : e = 1 := by omega
  exact h3 (by norm_num)

theorem a2l_chev3On_l2 (hGr : TBLit.GriessMultipliersOdd) (hCL2 : HypA2.ClosureFieldExp) :
    a2lChev3On fun S _ => ∃ e : ℕ, LieModel S .PSL 2 3 e := by
  intro K _ _ hK h2 _ hnF ⟨e, he⟩ σ hσ X hXσ hXc hXF
  have he2 : 2 ≤ e := a2l_two_le_of_psl_two_three he
  by_cases hZ : center K = ⊥
  · obtain ⟨σ', P, hPF, hF⟩ := a2l_exc_reduce hK hnF hσ hXσ hXc hXF
    haveI : IsSimpleGroup (K ⧸ center K) := hK.2.1
    have hq := CatLeaf.fixedTwoComponentsQuasisimple_psl_two hK.2.2 (p := 3) (by norm_num)
      (GH74.statedClassicalModel_of_lieModel (by norm_num) he)
    rcases a2l_fieldExp_of_fStar hCL2 hq he hPF hF with h | h | h | h
    · omega
    · subst h
      exact absurd (Or.inl he) hnF
    · subst h
      exact absurd (Or.inr (Or.inl he)) hnF
    · subst h
      exact Or.inl ⟨hZ, LieModel.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) he⟩
  · refine Or.inr (Or.inl (HypA2.centralDatum_of_psl_two hGr hK h2 hZ Nat.prime_three
      (by norm_num) ?_ he))
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2

end CFSG.OddStandard.SmallF3.HypA2Leaves
