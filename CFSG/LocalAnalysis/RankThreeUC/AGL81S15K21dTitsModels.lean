module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbedding.ParabHub

theorem solvOver_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel Y .PSL n 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact solvOver_of_borelQuotient
    (borelQuotient_sl ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (m + 1) F).trans e.symm))
    (fun i => rankOne_not_solvable_of_hasSL2Node hF4 (hasSL2Node_sl i)) hU

theorem solvOver_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel Y .PSp n 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact solvOver_of_borelQuotient (borelQuotient_sp e)
    (fun i => rankOne_not_solvable_of_hasSL2Node hF4 (hasSL2Node_sp i)) hU

section SpinMinus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabPrime

theorem rankOne_not_solvable_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF4 : 4 ≤ Nat.card F) (i : Fin (n - 1)) :
    ¬ Group.IsSolvable (rankOne (minusDatum n hirr).rootGroup i) := by
  by_cases hk : i.val + 1 < n - 1
  · exact rankOne_not_solvable_of_hasSL2Node hF4 (hasSL2Node_spinMinus_long hirr hk)
  have := fact_shortField hirr
  haveI : Group.IsPerfect (rankOne (minusDatum n hirr).rootGroup i) :=
    Subgroup.isPerfect_iff.2 ((rankOneNode_spinMinus_short hirr hk).perfect hF4)
  haveI : Nontrivial (rankOne (minusDatum n hirr).rootGroup i) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot => ?_
    have hx : (shortRels n hirr i).x 1 ∈ rankOne (minusDatum n hirr).rootGroup i :=
      Subgroup.mem_sup_left ((mem_minusRootGroup_single_iff hirr hk _).2 ⟨1, rfl⟩)
    rw [hbot, Subgroup.mem_bot] at hx
    exact one_ne_zero (shortRels_x_injective hirr i (hx.trans (shortRels n hirr i).x_zero.symm))
  exact Group.IsPerfect.not_isSolvable _

theorem solvOver_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact solvOver_of_borelQuotient (borelQuotient_spinMinus hirr hn e)
    (fun i => rankOne_not_solvable_spinMinus hirr hF4 i) hU

end SpinMinus

theorem solvOver_of_lieModel {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {m f : ℕ}
    (hf : 2 ≤ f) (ht : t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaMinus)
    (h : CFSG.Blueprint.LieModel Y t m 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  have hc : t ∈ CFSG.Blueprint.classicalTags → StatedClassicalModel Y t m 2 f :=
    CFSG.Blueprint.LieModel.statedClassicalModel h
  rcases ht with rfl | rfl | rfl | rfl
  · exact solvOver_of_model_psl hf (hc (by decide)) hU
  · exact solvOver_of_model_psp hf (hc (by decide)) hU
  · exact solvOver_of_model_psu hf (hc (by decide)) hU
  · exact solvOver_of_model_pomegaMinus hf (hc (by decide)) hU

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
