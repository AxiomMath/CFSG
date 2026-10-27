module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Gen
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

private theorem card_mulAut_alt {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6),
    Nat.card_perm, Nat.card_fin]

private theorem card_mulAut_alt_six_dvd :
    Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440 := by
  obtain ⟨hfin, hle⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have h720 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6))))
    rwa [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_perm, Nat.card_fin,
      show Nat.factorial 6 = 720 by decide] at h
  obtain ⟨k, hk⟩ := h720
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · exact ⟨2, by omega⟩
  · exact ⟨1, by omega⟩

theorem noElemSq_alt_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    NoElemSq p (alternatingGroup (Fin 5)) := by
  refine noElemSq_of_not_dvd hp ?_
  rw [card_mulAut_alt (by norm_num) (by norm_num)]
  intro h
  have : p ^ 2 ≤ 120 := Nat.le_of_dvd (by decide) h
  have : p ≤ 10 := by nlinarith
  interval_cases p <;> first | omega | (revert hp h; norm_num)

theorem noElemSq_alt_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    NoElemSq p (alternatingGroup (Fin 6)) := by
  refine noElemSq_of_not_dvd hp fun h => ?_
  have h' := h.trans card_mulAut_alt_six_dvd
  have : p ^ 2 ≤ 1440 := Nat.le_of_dvd (by decide) h'
  have : p ≤ 37 := by nlinarith
  interval_cases p <;> first | omega | (revert hp h'; norm_num)

theorem noElemSq_alt_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NoElemSq p (alternatingGroup (Fin 7)) := by
  refine noElemSq_of_not_dvd hp ?_
  rw [card_mulAut_alt (by norm_num) (by norm_num)]
  intro h
  have : p ^ 2 ≤ Nat.factorial 7 := Nat.le_of_dvd (by decide) h
  have : p ≤ 71 := by rw [show Nat.factorial 7 = 5040 by decide] at this; nlinarith
  interval_cases p <;> first | omega | (revert hp h; norm_num [Nat.factorial])

theorem noElemSq_gl_three_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    NoElemSq p (GL (Fin 3) (ZMod 2)) := by
  refine noElemSq_of_not_dvd hp ?_
  rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  intro h
  have : p ^ 2 ≤ 336 := Nat.le_of_dvd (by decide) h
  have : p ≤ 19 := by nlinarith
  interval_cases p <;> first | omega | (revert hp h; norm_num)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
