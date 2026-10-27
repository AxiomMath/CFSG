module

import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartOne.KS.Basic
import CFSG.GH74.KGroups.U33
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.RankThree.PartOne.Sec66T (innerAut)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open (IsQuasisimple)

theorem mem_innerAut_of_not_dvd_card_outer {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ Nat.card (Outer X)) {β : MulAut X} (hβ : β ^ p = 1) : β ∈ innerAut X := by
  have h1 : (QuotientGroup.mk β : Outer X) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk β : Outer X) ∣ p := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hp).mp h2 with h | h
  · have h3 : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      (QuotientGroup.eq_one_iff β).mp (orderOf_eq_one_iff.mp h)
    exact h3
  · exact absurd (h ▸ orderOf_dvd_natCard _) hnd

theorem false_of_alternating {X : Type} [Group X] [Finite X] {m p : ℕ} (hm : 5 ≤ m)
    (hp : p.Prime) (hp5 : 5 ≤ p) (e : X ≃* alternatingGroup (Fin m)) {α : MulAut X}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut X) : False := by
  have hout : Nat.card (Outer X) ≤ 4 :=
    (Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).trans_le
      (CFSG.RankThree.PartOne.card_outer_alternating_le_four hm)
  have hnd : ¬ p ∣ Nat.card (Outer X) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  exact hαinn (mem_innerAut_of_not_dvd_card_outer hp hnd hαp)

theorem false_of_psl_seven {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : StatedClassicalModel X .PSL 2 7 1) {α : MulAut X} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut X) : False := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := 7) (f := 1) (by norm_num) F (by simpa using hcard)).2 X
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  have h2 : Nat.card (Outer X) ∣ 2 := by simpa using hdvd
  have hnd : ¬ p ∣ Nat.card (Outer X) := fun hd => by
    have := Nat.le_of_dvd (by norm_num) (hd.trans h2)
    omega
  exact hαinn (mem_innerAut_of_not_dvd_card_outer hp hnd hαp)

section U33


theorem card_outer_le_two_of_psu_three_three {Y : Type} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (h : LieModel Y .PSU 3 3 1) : Nat.card (Outer Y) ≤ 2 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  have hA := CFSG.GH74.KGroups.U33.card_mulAut e
  have hY : Nat.card Y = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  have hI : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Y) = 6048 := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top, hY]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner Y)
  rw [hA, hI] at h1
  change 12096 = Nat.card (Outer Y) * 6048 at h1
  omega

theorem false_of_psu_three_three {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hnab : ∃ a b : X, a * b ≠ b * a) [IsSimpleGroup X]
    (h : StatedClassicalModel X .PSU 3 3 1) {α : MulAut X} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut X) : False := by
  have hinj := CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot
    (CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab)
  have hout := card_outer_le_two_of_psu_three_three hinj
    ((CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mpr h)
  have hnd : ¬ p ∣ Nat.card (Outer X) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  exact hαinn (mem_innerAut_of_not_dvd_card_outer hp hnd hαp)

end U33

end CFSG.AGLEmbedding.LieOut
