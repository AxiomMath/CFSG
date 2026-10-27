module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Input113

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem table112_T0 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → ∃ t : L, orderOf t = 2 := by
  intro L _ _ hq _
  have h2 : 2 ∣ Nat.card L := by
    by_contra h2
    have hodd : Odd (Nat.card L) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2
    have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
    have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial L
    exact this.ne hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨t, ht⟩

structure Tables112Rest : Prop where
  T1a : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 2
  T1b : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (CFSG.Open.pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1
  T2 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      2 * CFSG.Open.pRank p (Subgroup.center L) ≤ CFSG.Open.pRank p (⊤ : Subgroup L)
  T3 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      CFSG.Open.pRank p (Subgroup.center L) = 1 →
      (p = 3 ∧ Nat.card (Subgroup.center L) = 3) ∨
        p + 2 ≤ (p - 2) * CFSG.Open.pRank p (⊤ : Subgroup L)
  T11 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      2 ≤ CFSG.Open.pRank p (Subgroup.center L) →
      p = 3 ∧ CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup L) = 6 ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6
  T9 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 0 → CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2
  TFA_a : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 9 → FieldBonus L 3 H
  TFA_b : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 3 → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 27 → FieldBonus L 3 H

theorem tables112_of_rest (R : Tables112Rest) : Tables112 :=
  ⟨table112_T0, R.T1a, R.T1b, R.T2, R.T3, R.T11, R.T9, R.TFA_a, R.TFA_b⟩

theorem kernel11_2_of_rest (R : Tables112Rest) : Kernel11_2 :=
  kernel11_2_of_tables (tables112_of_rest R)

theorem input11_6_of_rest (R : Tables112Rest) (k : KernelT) : Input11_6 :=
  input11_6_of_tables (tables112_of_rest R) k

theorem input11_3_of_rest (R : Tables112Rest) (TL : TableL2) : Input11_3 :=
  input11_3_of_tables (tables112_of_rest R) TL

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
