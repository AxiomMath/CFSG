module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClOrthM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClWit
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverLieIndex)

theorem false_of_twistedA_three {S : Type} [Group S] [Finite S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) {α : MulAut S}
    (hP : U42Pumpup S α) : False := by
  have hT : catalogIs S S9.isU4two := ⟨.lie ⟨.twistedA 3 q, hv⟩, hq, ⟨e⟩⟩
  have hc : Nat.card S = 25920 := CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
  exact false_of_pumpup_of_card_le hP hc.le

theorem false_of_local81_group (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) (hRk : RkY Y) {d : TauCeti.ValidLieTypeIndex}
    (hd : ¬ TripleCoverLieIndex d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h : Local81 (TauCeti.CFSGIndex.lie d).Group) : False :=
  false_of_local81 hRk (cl_not_three_dvd_center hGA hY hd e) (h.congr e.symm)

theorem u42FieldTwoAt_classical_of (hGA : CFSG.Open.GriessAllModelsStatement)
    (hLO : LieOrderBridge) : U42FieldTwoAt U42Classical := by
  rintro Y _ _ hY - hRk d hd hc hf ⟨e⟩ α hα hP
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hn : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  cases d with
  | A n q =>
    have hq : q.card = 2 := hf
    exact (false_of_linear hGA hLO hY hRk hv hq e hP).elim
  | twistedA n q =>
    have hq : q.card = 2 := hf
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
    simp only [] at hr
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h6
    · exact (false_of_twistedA_three hv hq e hP).elim
    · exact Or.inr (Or.inr (Or.inl hq))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
    · exact (false_of_twistedA_high hGA hRk hv hq h6 e).elim
  | B n q =>
    have hq : q.card = 2 := hf
    obtain ⟨hp2, -⟩ := cl_primePower_card_two hq
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
    simp only [] at hr
    rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
    · exact (false_of_B_three hLO hn hv hq e hα hP).elim
    · exact Or.inl hq
    · refine (false_of_local81_group hGA hY hRk (d := ⟨.B n q, hv⟩) ?_ e
        (local81_B n q hv hp2 h5)).elim
      intro h
      simp only [TripleCoverLieIndex] at h
      omega
  | C n q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
    simp only [] at hr
    exact absurd ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hc) hr.2
  | D n q =>
    have hq : q.card = 2 := hf
    obtain ⟨hp2, -⟩ := cl_primePower_card_two hq
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
    simp only [] at hr
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    · exact Or.inr (Or.inl hq)
    · exact (false_of_local81_group hGA hY hRk (d := ⟨.D n q, hv⟩) (fun h => h) e
        (local81_D n q hv hp2 h5)).elim
  | twistedD n q =>
    have hq : q.card = 2 := hf
    obtain ⟨hp2, hexp⟩ := cl_primePower_card_two hq
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
    simp only [] at hr
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    · exact (false_of_twistedD_four hLO hn hv hq e hα hP).elim
    · exact (false_of_local81_group hGA hY hRk (d := ⟨.twistedD n q, hv⟩) (fun h => h) e
        (local81_twistedD n q hv hp2 hexp h5)).elim
  | _ => exact hd.elim

theorem u42FieldTwoAt_classical :
    U42FieldTwoAt U42Classical :=
  u42FieldTwoAt_classical_of
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
