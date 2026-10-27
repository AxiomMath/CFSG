module

public import Certificates.Certificate10131
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.KFacts.K426

theorem rep_j3WordArr :
    ∀ w : List ℕ, (∀ l ∈ w, l < 5) →
      Rep 6156 (j3WordArr w) (w.map CFSG.Sporadic.Schreier.j3Gen).prod
  | [], _ => by
    simp only [j3WordArr, List.foldr_nil, List.map_nil, List.prod_nil]
    exact rep_idA
  | l :: w, hw => by
    have ih := rep_j3WordArr w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    simp only [j3WordArr, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    exact rep_compA (CFSG.Sporadic.Schreier.rep_j3StrongPerm (hw l List.mem_cons_self)) ih

theorem prod_j3Gen_mem : ∀ w : List ℕ, (∀ l ∈ w, l < 2) →
    (w.map CFSG.Sporadic.Schreier.j3Gen).prod ∈ CFSG.Sporadic.Schreier.j3P
  | [], _ => by simp only [List.map_nil, List.prod_nil]; exact Subgroup.one_mem _
  | l :: w, hw => by
    simp only [List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ (prod_j3Gen_mem w fun z hz => hw z (List.mem_cons_of_mem _ hz))
    have hl := hw l List.mem_cons_self
    unfold CFSG.Sporadic.Schreier.j3P
    interval_cases l
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem i66_j3_real_XB :
    ∃ g ∈ CFSG.Sporadic.Schreier.j3P, g * j3tXB * g⁻¹ = j3tXB⁻¹ := by
  have hc := Certificates.certificate10131
  unfold j3RealBOK at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hw, he⟩ := hc
  set G := (j3RealBWord.map CFSG.Sporadic.Schreier.j3Gen).prod with hG
  have hRG : Rep 6156 (j3WordArr j3RealBWord) G :=
    rep_j3WordArr _ fun l hl => (hw l hl).trans (by norm_num)
  have hRX : Rep 6156 j3tReps[1]! j3tXB := rep_of_validA (j3tReps_spec (c := 1) (by norm_num)).1
  have h3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
  have e1 : G * j3tXB = (j3tXB * j3tXB) * G :=
    (eqA_iff (rep_compA hRG hRX) (rep_compA (rep_compA hRX hRX) hRG)).1 he
  refine ⟨G, prod_j3Gen_mem _ hw, ?_⟩
  calc G * j3tXB * G⁻¹ = (j3tXB * j3tXB) * G * G⁻¹ := by rw [e1]
    _ = j3tXB⁻¹ := by
        rw [mul_inv_cancel_right]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_two, ← pow_succ]; exact h3)

end CFSG.LocalAnalysis.GLTheoremA.CatB
