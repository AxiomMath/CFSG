module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBClasses
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoB
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBCommDefs
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open Subgroup CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB
open CFSG.ComponentClassification.RankTwoSporadic.B.Native CFSG.RankThree.Asc83Table.Native

theorem sub_one_eq_add_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : M - 1 = M + 1 := by
  have h : (-1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    ext i j
    rw [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> decide
  rw [sub_eq_add_neg, h]

theorem mul_sq_eq_one_of_commute {W : Type*} [Group W] {x y : W} (hyx : y * x = x * y)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) : (x * y) ^ 2 = 1 := by
  rw [(show Commute x y from hyx.symm).mul_pow, hx, hy, one_mul]

theorem mul_ne_one_of_ne {W : Type*} [Group W] {x y : W} (hx : x ^ 2 = 1) (hne : y ≠ x) :
    x * y ≠ 1 := fun h => hne (by
  rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx)])

theorem classFact_of_floor {W : Type*} [Group W] {r : W → ℕ} {f : ℕ}
    (hfloor : ∀ y : W, y ^ 2 = 1 → y ≠ 1 → f ≤ r y) {x : W} (hx2 : x ^ 2 = 1) (hrx : r x = f)
    {P : Subgroup W} (hP : ⁅P, P⁆ = P) (hPx : P ≤ centralizer {x})
    (hb : ∀ y ∈ centralizer (P : Set W), y * x = x * y → y ^ 2 = 1 → y ≠ 1 → y ≠ x →
      r y < f ∨ r (x * y) < f) : ClassFact r x := by
  refine ⟨P, hP, hPx, fun y hy hyx hy2 hy1 hyx' => ?_⟩
  rcases hb y hy hyx hy2 hy1 hyx' with h | h
  · omega
  · exact absurd h (not_lt.mpr (hfloor _ (mul_sq_eq_one_of_commute hyx hx2 hy2)
      (mul_ne_one_of_ne hx2 hyx')))

theorem rankB_eq (X : NativeSporadic.B) : rankB X = (X.val.val + 1).rank := by
  unfold rankB
  rw [sub_one_eq_add_one]

theorem twoB_classFact
    : ClassFact rankB (classRep 0) := by
  obtain ⟨P, hP, hPx, hC⟩ := twoB_perfect_centralizer
  have hx2 : xTwoB ^ 2 = 1 := by
    rw [sq, xTwoB, ← map_mul, rs_mul_self (by norm_num), map_one]
  exact ⟨P, hP, hPx, fun y hy _ _ hy1 hyx => by
    rcases eq_one_or_eq_of_mem_zpowers hx2 (hC hy) with h | h
    · exact absurd h hy1
    · exact absurd h hyx⟩

@[expose] def TwoAClassData : Prop :=
  ∃ x : NativeSporadic.B, x ^ 2 = 1 ∧ x ≠ 1 ∧ (x.val.val + 1).rank ≤ 1860 ∧
    ∃ P : Subgroup NativeSporadic.B, ⁅P, P⁆ = P ∧ P ≤ centralizer {x} ∧
      ∀ y ∈ centralizer (P : Set NativeSporadic.B), y * x = x * y → y ^ 2 = 1 → y ≠ 1 →
        y ≠ x → (y.val.val + 1).rank ≤ 1859 ∨ ((x * y).val.val + 1).rank ≤ 1859

theorem twoA_classFact_of_check
    (h : TwoAClassData) : ∃ x : NativeSporadic.B, x ^ 2 = 1 ∧ x ≠ 1 ∧
      rankB x = rankB (classRep 1) ∧ ClassFact rankB x := by
  obtain ⟨-, h1, -, -, -⟩ := classes_B
  obtain ⟨x, hx2, hx1, hxr, P, hP, hPx, hb⟩ := h
  have hfloor : ∀ y : NativeSporadic.B, y ^ 2 = 1 → y ≠ 1 → 1860 ≤ rankB y := by
    intro y hy2 hy1
    rcases rankB_of_involution hy2 hy1 with h' | h' | h' | h' <;> omega
  have hxB : rankB x = 1860 := by
    have hle : rankB x ≤ 1860 := (rankB_eq x).trans_le hxr
    have := hfloor x hx2 hx1
    omega
  refine ⟨x, hx2, hx1, hxB.trans h1.symm, classFact_of_floor hfloor hx2 hxB hP hPx ?_⟩
  intro y hy hyx hy2 hy1 hyx'
  rcases hb y hy hyx hy2 hy1 hyx' with h' | h'
  · left
    have h'' : (y.val.val + 1).rank ≤ 1859 := h'
    rw [rankB_eq]
    omega
  · right
    have h'' : ((x * y).val.val + 1).rank ≤ 1859 := h'
    rw [rankB_eq]
    omega

@[expose] def B2CFact
    : Prop := ClassFact rankB (classRep 5)

@[expose] def B2DFact
    : Prop := ClassFact rankB (classRep 3)

theorem sporadicCaseOdd_B_of_facts
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) (h2A : TwoAClassData)
    (h2C : B2CFact) (h2D : B2DFact) : SporadicCaseOdd .B := by
  refine sporadicCaseOdd_of_perfectCentralizerBound h32 h33 (s := .B)
    CFSG.RankThree.PartOne.SPOR.allInner_B (r := rankB) (perfectCentralizerBound_B ?_)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have hrep : ∀ j, j < 14 → classRep j ^ 2 = 1 ∧ classRep j ≠ 1 := fun j hj =>
    ⟨by rw [sq, classRep, ← map_mul, rs_mul_self hj, map_one],
      fun h => rs_ne_one hj (by simpa [classRep] using congrArg iotaEquiv h)⟩
  rcases hi with rfl | rfl | rfl | rfl
  · exact twoA_classFact_of_check h2A
  · exact ⟨_, (hrep 0 (by norm_num)).1, (hrep 0 (by norm_num)).2, rfl, twoB_classFact⟩
  · exact ⟨_, (hrep 5 (by norm_num)).1, (hrep 5 (by norm_num)).2, rfl, h2C⟩
  · exact ⟨_, (hrep 3 (by norm_num)).1, (hrep 3 (by norm_num)).2, rfl, h2D⟩

end CFSG.ComponentClassification.RankTwoSporadic.B
