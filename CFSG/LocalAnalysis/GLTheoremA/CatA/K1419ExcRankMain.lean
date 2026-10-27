module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRankPump
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRankInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Dickson.Sec6 (FamG2 FamTriD4 FamReeF4)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innerAut

section Exc


theorem l3u3Rank_exc {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : FamG2 d.1 ∨ FamTriD4 d.1 ∨ FamReeF4 d.1)
    (hc : CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d.1)
    (e : S ≃* (CFSGIndex.lie d).Group) : innAutDerived S ≤ innerAut S ∧ RankLE2 3 S := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q => exact l3u3Rank_g2 q hv hc e
  | trialityD4 q => exact l3u3Rank_triD4 q hv hc e
  | reeF4 m => exact l3u3Rank_reeF4 hv e
  | _ => rcases hd with hd | hd | hd <;> exact hd.elim

end Exc

section Main


theorem l3u3Rank_center_eq_bot (hF : L3U3Facts) {X : Type} [Group X] [Finite X] (h : L3U3 X) :
    Subgroup.center X = ⊥ := by
  haveI := l3u3Plumb_isSimpleGroup h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a
    let _ : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := X)
    rcases hp.eq_one_or_self_of_dvd 9 (L3U3Order.nine_dvd (hF.order X h)) with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp

theorem excRankRes_holds (hF : L3U3Facts) : ExcRankRes := by
  intro S _ _ d hd hc e β hβ hP
  obtain ⟨hinn, hrank⟩ := l3u3Rank_exc d hd hc e
  have hsimple : IsSimpleGroup S :=
    e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
  obtain ⟨x, rfl⟩ := hinn hβ
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
    · exact h0
    · exfalso
      have hx : x ∈ Subgroup.center S := h0 ▸ Subgroup.mem_top x
      refine hP.2.1 (MulEquiv.ext fun s => ?_)
      rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hx s,
        mul_inv_cancel_right]
  obtain ⟨E, hE, hlt⟩ := L3U3Pumpup.exists_elemAbelian_gt_nine hF
    (fun _ _ _ hX => l3u3Rank_center_eq_bot hF hX) hZ hP
  have := hrank E hE
  omega

end Main

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
