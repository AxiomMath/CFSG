module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67N2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.OddAut

section Dispatch

variable {K : Type} [Field K] [Finite K]

theorem natCast_eq_one_iff {r q : ℕ} (hq : 1 ≤ q) : (q : ZMod r) = 1 ↔ r ∣ q - 1 := by
  rw [← Nat.cast_one (R := ZMod r), ZMod.natCast_eq_natCast_iff]
  exact ⟨fun h => (Nat.modEq_iff_dvd' hq).mp h.symm, fun h => ((Nat.modEq_iff_dvd' hq).mpr h).symm⟩

theorem false_of_inner_Ln45 {n : ℕ} (hn : n = 4 ∨ n = 5) {r : ℕ} [Fact r.Prime] (hr2 : Odd r)
    (hrK : ¬ r ∣ Nat.card K) {V Z : Subgroup (MulAut (projectiveSL n K))}
    (h2 : N2Cfg (projectiveSL n K) r V Z)
    (hVD : ∀ v ∈ V, ∃ A : GL (Fin n) K, v = conjAut n K A)
    (he1 : r ∣ Nat.card K - 1 → False) (he2 : (Nat.card K : ZMod r) = -1 → False) : False := by
  classical
  have hr : r.Prime := Fact.out
  have hn3 : 3 ≤ n := by omega
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  by_cases hA : r ∣ Nat.card K - 1
  · exact he1 hA
  · have hq1' : (Nat.card K : ZMod r) ≠ 1 := fun h => hA ((natCast_eq_one_iff hq1).mp h)
    by_cases hdiv : n / orderOf (Nat.card K : ZMod r) ≤ 1
    · have : IsElementaryAbelian r ↥V := hVe
      obtain ⟨W, hWe, hWc, -, -⟩ := Ln.exists_lift_group (K := K) (n := n) hn3 hA hVc hVD
      have := hWe
      exact Ln.false_of_sylow_cyclic W hWc (fun P => Ln.isCyclic_sylow_gl_of_div hr2 hrK hdiv P)
    ·
      push Not at hdiv
      set e := orderOf (Nat.card K : ZMod r) with he
      have he0 : e ≠ 0 := by
        intro h0
        rw [h0] at hdiv
        simp at hdiv
      have he1' : e ≠ 1 := by
        intro h1
        exact hq1' (orderOf_eq_one_iff.mp h1)
      have he2' : e ≤ 2 := by
        by_contra hgt
        push Not at hgt
        have : n / e < 2 := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega
      have he2'' : e = 2 := by omega
      have hsq : (Nat.card K : ZMod r) ^ 2 = 1 := by
        rw [← he2'']; exact pow_orderOf_eq_one _
      have hfield : (Nat.card K : ZMod r) = 1 ∨ (Nat.card K : ZMod r) = -1 := by
        have h : ((Nat.card K : ZMod r) - 1) * ((Nat.card K : ZMod r) + 1) = 0 := by
          linear_combination hsq
        rcases mul_eq_zero.mp h with h | h
        · left; exact sub_eq_zero.mp h
        · right; exact eq_neg_of_add_eq_zero_left h
      rcases hfield with h | h
      · exact absurd h hq1'
      · exact he2 h

end Dispatch

end CFSG.GH74.GLS.Stage2.Bender.Thm1

