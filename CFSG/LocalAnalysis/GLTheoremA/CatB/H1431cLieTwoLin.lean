module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

theorem lieSTwo_false_of_linear (hGA : CFSG.Open.GriessAllModelsStatement)
    (hLO : LieOrderBridge) {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hRk : RkY Y) {n : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (hq : q.card = 2)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group)
    {α : MulAut (Y ⧸ Subgroup.center Y)} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {J : Subgroup (Y ⧸ Subgroup.center Y)} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (h4 : 3 ^ 4 ∣ Nat.card (PSimple 3 J)) : False := by
  obtain ⟨hp2, hf1⟩ := I1431C2.cl_primePower_card_two hq
  have hn4 := I1431C2.lin_four_le_of_valid hv hq
  have hmodel : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL (n + 1) 2 1 := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA n q hv
    have h' := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (h.2.resolve_right fun h0 => absurd h0.1 (Nat.succ_ne_zero n))
    rwa [hp2, hf1] at h'
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := I1431C2.cl_center_eq_bot_of_simple
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY)
    have hcard : Nat.card (Y ⧸ Subgroup.center Y) = orderA n 2 := by
      rw [hLO ⟨.A n q, hv⟩ _ ⟨e⟩]
      exact congrArg (orderA n) hq
    exact lieSTwo_false_of_inner hZ hα3 hα1 hJ h4
      (I1431C2.lin_inner_of_model hmodel (by omega) hα3)
      (by rw [hcard]; exact I1431C2.lin_not_dvd_orderA hn4 (by omega))
  · have hd : ¬ CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex (.A n q) := by
      rintro ⟨-, h3⟩
      rw [hq] at h3
      omega
    exact I1431C2.false_of_local81 hRk
      (I1431C2.cl_not_three_dvd_center hGA hY (d := ⟨.A n q, hv⟩) hd e)
      (I1431C2.lin_local81_of_model hmodel (by omega))

theorem lieSTwoAt_linear (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge) :
    LieSTwoAt fun d => ∃ n q, d = .A n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α - hα3 hα1
  have hq : q.card = 2 := hf
  exact lieSTwo_of_no_pump hLO fun J hJ h4 =>
    lieSTwo_false_of_linear hGA hLO hY hRk hv hq e hα3 hα1 hJ h4

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
