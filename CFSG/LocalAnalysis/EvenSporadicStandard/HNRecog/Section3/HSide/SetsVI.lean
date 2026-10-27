module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Labelled
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {b z : G} {z₀ b₀ u₀ : ↥(Gx b)}

private theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine SemiconjBy.orderOf_eq c ?_
  change c * x = y * c
  rw [← hc, mul_assoc, inv_mul_cancel, mul_one]

private theorem shapeFiveC_Gxy_iff {B x : G} (hx : x ∈ Gx B) :
    IsShapeCentralizerFiveC ↥(Gxy B x) ↔
      IsShapeCentralizerFiveC ↥(Gx (⟨x, hx⟩ : ↥(Gx B))) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gxy (G := G) (a := B) (x := x) hx
  exact ⟨fun h => IsShapeCentralizerFiveC.of_mulEquiv e h,
    fun h => IsShapeCentralizerFiveC.of_mulEquiv e.symm h⟩

private theorem shapeFiveB_Gxy_iff {B x : G} (hx : x ∈ Gx B) :
    IsShapeCentralizerFiveB ↥(Gxy B x) ↔
      IsShapeCentralizerFiveB ↥(Gx (⟨x, hx⟩ : ↥(Gx B))) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gxy (G := G) (a := B) (x := x) hx
  exact ⟨fun h => IsShapeCentralizerFiveB.of_mulEquiv e h,
    fun h => IsShapeCentralizerFiveB.of_mulEquiv e.symm h⟩

theorem tBase_eq (L : HLab b z z₀ b₀ u₀) {y : ↥(Gx b)} (hy : IsConj (GxSelf b * z₀) y) :
    tBase (y : G) z b = Subtype.val '' tab6Base (GxSelf b) z₀ y := by
  have hy' := (L.isConj_bz₀_iff y).mp hy
  have hba : IsConj b (y : G) := hy'.1
  have hzbc : IsConj z (b * (y : G)) := hy'.2
  have horder_b : orderOf b = 2 := by
    show orderOf ((GxSelf b : ↥(Gx b)) : G) = 2
    rw [Subgroup.orderOf_coe, L.facts.orderOf_a]
  have horder_z : orderOf z = 2 := by
    rw [orderOf_eq_of_isConj L.z₀_B]
    show orderOf ((z₀ : ↥(Gx b)) : G) = 2
    rw [Subgroup.orderOf_coe, L.facts.orderOf_z]
  have horder_a : orderOf (y : G) = 2 := by
    rw [← orderOf_eq_of_isConj hba, horder_b]
  have ha2 : (y : G) ^ 2 = 1 := by
    rw [← horder_a]; exact pow_orderOf_eq_one _
  have hz2 : z ^ 2 = 1 := by
    rw [← horder_z]; exact pow_orderOf_eq_one _
  have memGx : ∀ {c : G}, IsConj (y : G) c → IsConj z (b * c) → c ∈ Gx b := by
    intro c hca hcz
    exact mem_Gx_of_isConj_mul (x := (y : G)) (y := z) (b := b) (c := c)
      ha2 hz2 hba.symm hca (Or.inr hcz)
  apply Set.Subset.antisymm
  · intro c hc
    simp only [tBase, Set.mem_setOf_eq] at hc
    obtain ⟨hca, hcz, hcne⟩ := hc
    have hcGx : c ∈ Gx b := memGx hca hcz
    refine ⟨⟨c, hcGx⟩, ?_, rfl⟩
    simp only [tab6Base, Set.mem_setOf_eq]
    refine ⟨(L.isConj_bz₀_iff ⟨c, hcGx⟩).mpr ⟨IsConj.trans hba hca, hcz⟩, ?_⟩
    intro h
    exact hcne (congrArg Subtype.val h)
  · rintro d ⟨c', hc', rfl⟩
    simp only [tab6Base, Set.mem_setOf_eq] at hc'
    obtain ⟨hconj, hne⟩ := hc'
    obtain ⟨hbc', hzbc'⟩ := (L.isConj_bz₀_iff c').mp hconj
    simp only [tBase, Set.mem_setOf_eq]
    exact ⟨IsConj.trans hba.symm hbc', hzbc', fun h => hne (Subtype.ext h)⟩

private theorem image_tBase_of_pred (L : HLab b z z₀ b₀ u₀) {y : ↥(Gx b)}
    (hy : IsConj (GxSelf b * z₀) y) {P : G → Prop} {Q : ↥(Gx b) → Prop}
    (hPQ : ∀ c' ∈ tab6Base (GxSelf b) z₀ y, P (c' : G) ↔ Q c') :
    {c : G | c ∈ tBase (y : G) z b ∧ P c} =
      Subtype.val '' {c' : ↥(Gx b) | c' ∈ tab6Base (GxSelf b) z₀ y ∧ Q c'} := by
  apply Set.Subset.antisymm
  · rintro c ⟨hc, hPc⟩
    have hmem : c ∈ Subtype.val '' tab6Base (GxSelf b) z₀ y := by
      rw [← tBase_eq L hy]; exact hc
    obtain ⟨c', hc', rfl⟩ := hmem
    exact ⟨c', ⟨hc', (hPQ c' hc').mp hPc⟩, rfl⟩
  · rintro d ⟨c', ⟨hc', hQc'⟩, rfl⟩
    have hc : (c' : G) ∈ tBase (y : G) z b := by
      rw [tBase_eq L hy]; exact ⟨c', hc', rfl⟩
    exact ⟨hc, (hPQ c' hc').mpr hQc'⟩

theorem tSet_eq (L : HLab b z z₀ b₀ u₀) {y : ↥(Gx b)} (hy : IsConj (GxSelf b * z₀) y) (i : Fin 8) :
    tSet (y : G) z b i = Subtype.val '' tab6Set (GxSelf b) z₀ b₀ u₀ y i := by
  have hy' := (L.isConj_bz₀_iff y).mp hy
  have hba : IsConj b (y : G) := hy'.1
  fin_cases i
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change IsConj (y : G) ((y * c' : ↥(Gx b)) : G) ↔ HIsA (GxSelf b) z₀ b₀ (y * c')
    rw [L.isA_iff]
    exact ⟨fun h => hba.trans h, fun h => hba.symm.trans h⟩
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change IsConj z ((y * c' : ↥(Gx b)) : G) ↔ HIsB z₀ u₀ (y * c')
    rw [L.isB_iff]
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change orderOf ((y * c' : ↥(Gx b)) : G) = 3 ↔ orderOf (y * c') = 3
    rw [← Subgroup.orderOf_coe (y * c')]
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change (orderOf ((y * c' : ↥(Gx b)) : G) = 4 ∧
        IsConj z (((y * c' : ↥(Gx b)) : G) ^ 2)) ↔
      (orderOf (y * c') = 4 ∧ HIsB z₀ u₀ ((y * c') ^ 2))
    rw [L.isB_iff, ← Subgroup.orderOf_coe (y * c'), Subgroup.coe_pow]
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change (orderOf ((y * c' : ↥(Gx b)) : G) = 4 ∧
        IsConj (y : G) (((y * c' : ↥(Gx b)) : G) ^ 2)) ↔
      (orderOf (y * c') = 4 ∧ HIsA (GxSelf b) z₀ b₀ ((y * c') ^ 2))
    rw [L.isA_iff, ← Subgroup.orderOf_coe (y * c'), Subgroup.coe_pow]
    exact ⟨fun h => ⟨h.1, hba.trans h.2⟩, fun h => ⟨h.1, hba.symm.trans h.2⟩⟩
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change (orderOf ((y * c' : ↥(Gx b)) : G) = 5 ∧
        IsShapeCentralizerFiveC ↥(Gxy b ((y * c' : ↥(Gx b)) : G))) ↔
      (orderOf (y * c') = 5 ∧ IsShapeCentralizerFiveC ↥(Gx (y * c')))
    rw [← Subgroup.orderOf_coe (y * c')]
    have hiff := shapeFiveC_Gxy_iff (G := G) (B := b) (x := (y * c' : ↥(Gx b))) (y * c').2
    have helem : (⟨((y * c' : ↥(Gx b)) : G), (y * c').2⟩ : ↥(Gx b)) = y * c' :=
      Subtype.ext rfl
    rw [hiff, helem]
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change (orderOf ((y * c' : ↥(Gx b)) : G) = 5 ∧
        IsShapeCentralizerFiveB ↥(Gxy b ((y * c' : ↥(Gx b)) : G))) ↔
      (orderOf (y * c') = 5 ∧ IsShapeCentralizerFiveB ↥(Gx (y * c')))
    rw [← Subgroup.orderOf_coe (y * c')]
    have hiff := shapeFiveB_Gxy_iff (G := G) (B := b) (x := (y * c' : ↥(Gx b))) (y * c').2
    have helem : (⟨((y * c' : ↥(Gx b)) : G), (y * c').2⟩ : ↥(Gx b)) = y * c' :=
      Subtype.ext rfl
    rw [hiff, helem]
  · simp only [tSet, tab6Set]
    apply image_tBase_of_pred L hy
    intro c' _
    change (orderOf ((y * c' : ↥(Gx b)) : G) = 6 ∧
        IsConj (y : G) (((y * c' : ↥(Gx b)) : G) ^ 3)) ↔
      (orderOf (y * c') = 6 ∧ HIsA (GxSelf b) z₀ b₀ ((y * c') ^ 3))
    rw [L.isA_iff, ← Subgroup.orderOf_coe (y * c'), Subgroup.coe_pow]
    exact ⟨fun h => ⟨h.1, hba.trans h.2⟩, fun h => ⟨h.1, hba.symm.trans h.2⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3