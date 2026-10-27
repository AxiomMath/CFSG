module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddTwo

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  CFSG.HardMathSupport.Lang.E6Descent

section Leaves


theorem triOdd_d4OuterThreeEll : D4OuterThreeEll := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ n hn hnT hN
  obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
    ellQ1_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
  exact (d4OuterThreeA2Toral_thm p f hp hp2 hp3 hf hq K hK σ hσ d hd hd3 hd1 s hsd).of_conj_eq _
    hconj

theorem triOdd_d4OuterThreeEllMinus : D4OuterThreeEllMinus := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ n hn hN
  obtain ⟨y₀, s, hsT, hconj⟩ := minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hN
  exact (d4OuterThreeA2Minus_thm p f hp hp2 hp3 hf hq K hK σ hσ s hsT).of_conj_eq _ hconj

theorem triOdd_d4OuterThreeMinus : D4OuterThreeMinus :=
  d4Minus_of_stages d4MinusNF d4OuterThreeA2Minus_thm triOdd_d4OuterThreeEllMinus

theorem triOdd_d4OuterThree : D4OuterThree :=
  d4OuterThree_of_leaves d4OuterThreeA2Toral_thm triOdd_d4OuterThreeEll triOdd_d4OuterThreeMinus

end Leaves

section Fixed

theorem triOdd_exists_fixed_not_mem_zpowers {Y : Type} [Group Y] {φ : MulAut Y} (h : D4NoAbel φ)
    {x : Y} (hx : φ x = x) (hx1 : x ≠ 1) :
    ∃ y : Y, φ y = y ∧ y * x * y⁻¹ ∉ Subgroup.zpowers x := by
  by_contra hcon
  push Not at hcon
  have hxs : x ∈ fixSub φ := hx
  let F₀ : Subgroup (fixSub φ) := (Subgroup.zpowers x).subgroupOf (fixSub φ)
  have hnorm : F₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Y) ∈ Subgroup.zpowers x := hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn'
    show ((g * n * g⁻¹ : fixSub φ) : Y) ∈ Subgroup.zpowers x
    have h1 : ((g * n * g⁻¹ : fixSub φ) : Y) = (g : Y) * (n : Y) * (g : Y)⁻¹ := rfl
    rw [h1, ← hk, ← conj_zpow]
    exact Subgroup.zpow_mem _ (hcon (g : Y) g.2) k
  have hab : ∀ a b : F₀, a * b = b * a := by
    intro a b
    have ha : (a : fixSub φ).1 ∈ Subgroup.zpowers x := a.2
    have hb : (b : fixSub φ).1 ∈ Subgroup.zpowers x := b.2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb
    apply Subtype.ext
    apply Subtype.ext
    show (a : fixSub φ).1 * (b : fixSub φ).1 = (b : fixSub φ).1 * (a : fixSub φ).1
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hbot := h F₀ hnorm hab
  have hmem : (⟨x, hxs⟩ : fixSub φ) ∈ F₀ := Subgroup.mem_zpowers x
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx1 (congrArg Subtype.val hmem)

end Fixed

end CFSG.LieType.SeitzGeneration.ExcWideThree
