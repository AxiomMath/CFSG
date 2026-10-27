module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactAutA6_holds : KFactAutA6 := by
  obtain ⟨hfin, hle⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by norm_num)
  have h720 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6))))
    have hc : Nat.card (MonoidHom.range
        (MulAut.conjNormal (H := alternatingGroup (Fin 6)))) = 720 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
      rfl
    rwa [hc] at h
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  obtain ⟨k, hk⟩ := h720
  rw [KFactAutA6, hk]
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exact ⟨2, by norm_num⟩
  · exact ⟨1, by norm_num⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
