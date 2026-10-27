module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem lin_four_le_of_valid {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n q).Valid) (hq : q.card = 2) : 4 ≤ n := by
  obtain ⟨hr, hdup⟩ := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  obtain ⟨h1, h2⟩ := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hr
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  by_contra hlt
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
  · have := h2 rfl
    omega
  · exact hdup (Or.inr (Or.inl ⟨rfl, hq⟩))
  · exact hdup (Or.inr (Or.inr ⟨rfl, hq⟩))

theorem lin_inner_of_model {X : Type} [Group X] {m : ℕ} (h : StatedClassicalModel X .PSL m 2 1)
    (hm : 3 ≤ m) {α : MulAut X} (hα : α ^ 3 = 1) : α ∈ inner X := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one h
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec21.Hering214.inner_of_pow_three_eq_one hK hm
    (α := MulAut.congr φ α) (by rw [← map_pow, hα, map_one])
  refine ⟨φ.symm y, (MulAut.congr φ).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem lin_not_dvd_orderA {n : ℕ} (h4 : 4 ≤ n) (h6 : n ≤ 6) : ¬ 3 ^ 5 ∣ orderA n 2 := by
  interval_cases n <;> decide +kernel

theorem lin_local81_psl {K : Type} [Field K] [CharP K 2] [Finite K] {m : ℕ} (hm : 8 ≤ m) :
    Local81 (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) := by
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) :=
    CFSG.RankThree.PartTwo.Census.four_le_localRank_PSL_of_eight_le hm
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three (by norm_num) h4
  exact ⟨U, hU2, hU1, E, hEN, isElemAbelian_iff_isElementaryAbelian.2 hEe, hEc⟩

theorem lin_local81_of_model {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL m 2 1) (hm : 8 ≤ m) : Local81 X := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one h
  haveI := CFSG.RankThree.PartTwo.Sec21.Hering214.charP_two_of_natCard_eq_two hK
  exact Local81.congr (φ.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL m
      K).symm).symm (lin_local81_psl hm)

theorem false_of_linear (hGA : CFSG.Open.GriessAllModelsStatement)
    (hLO : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hRk : CFSG.HardMathSupport.Dickson.Sec6.I1431.RkY Y)
    {n : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A n q).Valid) (hq : q.card = 2)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group)
    {α : MulAut (Y ⧸ Subgroup.center Y)} (hP : U42Pumpup (Y ⧸ Subgroup.center Y) α) : False := by
  obtain ⟨hp2, hf1⟩ := cl_primePower_card_two hq
  have hn4 := lin_four_le_of_valid hv hq
  have hmodel : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL (n + 1) 2 1 := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA n q hv
    have h' := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (h.2.resolve_right fun h0 => absurd h0.1 (Nat.succ_ne_zero n))
    rwa [hp2, hf1] at h'
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := cl_center_eq_bot_of_simple
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY)
    have hcard : Nat.card (Y ⧸ Subgroup.center Y) = orderA n 2 := by
      rw [hLO ⟨.A n q, hv⟩ _ ⟨e⟩]
      exact congrArg (orderA n) hq
    exact false_of_pumpup_of_inner hZ hP (lin_inner_of_model hmodel (by omega) hP.1)
      (by rw [hcard]; exact lin_not_dvd_orderA hn4 (by omega))
  · have hd : ¬ CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex (.A n q) := by
      rintro ⟨-, h3⟩
      rw [hq] at h3
      omega
    exact false_of_local81 hRk (cl_not_three_dvd_center hGA hY (d := ⟨.A n q, hv⟩) hd e)
      (lin_local81_of_model hmodel (by omega))

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
