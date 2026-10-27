module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def LieOuterRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

@[expose] def LieCoverRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → LieCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def SporadicCoverRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → SporCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L) + 1

@[expose] def T1bLie : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (CFSG.Open.pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1

theorem pRank_mulAut_le_mulAut_centerQuotient {L : Type*} [Group L] [Finite L]
    (hperf : commutator L = ⊤) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (L ⧸ Subgroup.center L))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _
    (autCenterQuot_injective_of_perfect hperf)

theorem pRank_centerQuotient_le_of_not_dvd {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have : Fact p.Prime := ⟨hp⟩
  exact (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) hZ).le

end CFSG.HardMathSupport.Timmesfeld.Coordinator
