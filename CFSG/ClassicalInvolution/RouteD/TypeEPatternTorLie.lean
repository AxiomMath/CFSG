module

public import CFSG.ClassicalInvolution.RouteD.GapsFrLie

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups commutatorElement

section Closure

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  {F : HypFrame Q m} {Fix : Subgroup (spinGroup Q)}

theorem rootInN_of_A_chain {n : ℕ}
    (hA : ∀ a, a < n → RootInN F Fix a (a + 1) true false ∧ RootInN F Fix (a + 1) a true false) :
    ∀ a b, a ≤ n → b ≤ n → a ≠ b → RootInN F Fix a b true false := by
  have st1 : ∀ d a, a + d + 1 ≤ n → RootInN F Fix a (a + d + 1) true false := by
    intro d
    induction d with
    | zero => exact fun a h => (hA a (by omega)).1
    | succ d ih =>
      intro a h
      have h1 := ih a (by omega)
      have h2 := (hA (a + d + 1) (by omega)).1
      have := RootInN.comm (u := false) (t := false) h1 h2 (by omega)
      have e : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [e]
      exact this
  have st2 : ∀ d a, a + d + 1 ≤ n → RootInN F Fix (a + d + 1) a true false := by
    intro d
    induction d with
    | zero => exact fun a h => (hA a (by omega)).2
    | succ d ih =>
      intro a h
      have h1 := (hA (a + d + 1) (by omega)).2
      have h2 := ih a (by omega)
      have := RootInN.comm (u := false) (t := false) h1 h2 (by omega)
      have e : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [e]
      exact this
  intro a b ha hb hab
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
    exact st1 d a hb
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + d + 1 := ⟨a - b - 1, by omega⟩
    exact st2 d b ha

theorem rootSL2_le_of_rootInN {a b : ℕ} (h1 : RootInN F Fix a b true false)
    (h2 : RootInN F Fix b a true false) :
    ∃ (ha : a < m) (hb : b < m) (hab : a ≠ b),
      (F.longSL2 (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (fun h => hab (congrArg Fin.val h)) true
        false).range ≤ Fix := by
  obtain ⟨ha, hb, hab, h1⟩ := h1
  obtain ⟨hb', ha', hba, h2⟩ := h2
  refine ⟨ha, hb, hab, ?_⟩
  rw [longSL2_range_eq_sup, sup_le_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact h1 (Multiplicative.toAdd c)
  · rintro _ ⟨c, rfl⟩
    exact h2 (Multiplicative.toAdd c)

theorem rootInN_pair_of_longSL2_le {a : ℕ} (ha : a < m) (hb : a + 1 < m)
    (h : (F.longSL2 (i := ⟨a, ha⟩) (j := ⟨a + 1, hb⟩)
      (fun e => absurd (congrArg Fin.val e) (by simp)) true false).range ≤ Fix) :
    RootInN F Fix a (a + 1) true false ∧ RootInN F Fix (a + 1) a true false := by
  have hab : a ≠ a + 1 := by omega
  have hba : a + 1 ≠ a := by omega
  rw [longSL2_range_eq_sup, sup_le_iff] at h
  refine ⟨⟨ha, hb, hab, fun c => h.1 ⟨.ofAdd c, rfl⟩⟩, ⟨hb, ha, hba, fun c => ?_⟩⟩
  exact h.2 ⟨.ofAdd c, rfl⟩

end Closure

end CFSG.ClassicalInvolution.RouteD.Gaps
