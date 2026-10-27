module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyTwoB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem i1016M5Fact_of_parts (ha : TwoLocalRankCriterion) (hb : Co1FiveCubeFacts)
    (hc : BabyFiveRankFact) : I1016M5Fact := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  have hG5 : ∀ A : Subgroup MGriess, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess)) = twoBCentralizerOrder := by
    intro A hAc hAe h8
    obtain ⟨-, a, z, ha2, hz, -, hcls, hA, hB, hgraph⟩ := id hE
    obtain ⟨-, c, -, -, hc1, -, -, -, -, hshape, -⟩ := hgraph
    obtain ⟨u, hu, hzu⟩ := exists_twoB_of_elemAbelian babyTableIII babyTableIV
      MonsterTwoBGmat.nineteen_dvd_of_lieModel ha2 hA hc1 hshape hcls A hAc hAe h8
    refine ⟨u, hu, ?_, (hB u hzu).2.2.2.2.1⟩
    obtain ⟨g, hg⟩ := isConj_iff.1 hzu
    have h := MulEquiv.orderOf_eq (MulAut.conj g) z
    rw [MulAut.conj_apply, hg, hz] at h
    exact h
  have hM : GLATwoLocalRank 5 MGriess ≤ 3 :=
    ha MGriess 5 3 4 Nat.prime_five (by norm_num)
      (fun j hj0 hj4 => by interval_cases j <;> decide) (card_le_of_involution hE hb hc)
      (false_of_twoB hE card_nativeB hG5 hb)
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  obtain ⟨e₁⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  intro K _ _ hK
  obtain ⟨i, hi, ⟨φ⟩⟩ := hK
  simp only [S8.sporIs] at hi
  subst hi
  have ψ : K ≃* MGriess := φ.trans (e₀.trans e₁).symm
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (p := 5)
    (by norm_num) ψ
  omega

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5
