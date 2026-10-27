module

public import CFSG.CGT.PushingUpLit.T2KR.PairStar
public import CFSG.CGT.PushingUpLit.T2KR.Count4

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

@[expose] def Print65Torus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G),
    Sit64 G L M T n D g →
    2 < (normIn (QOf L M) (Aof L M g)).relIndex (QOf L M) →
      ∃ h ∈ M, ∀ x ∈ normIn (Aof L M g) (QOf L M),
        ∃ x' ∈ normIn (Aof L M g) (QOf L M), ∃ d ∈ D, x = ⁅x', h⁆ * d

@[expose] def Print66D1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (g : G),
    Sit64 G L M T n ⊥ g → False

@[expose] def Print611Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G)
    (hE1 : FooteNonsolvableSimple) (hs : Sit64 G L M T n D g),
    PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D → Nat.card D = 2 → False

@[expose] def Print612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G)
    (hE1 : FooteNonsolvableSimple) (hs : Sit64 G L M T n D g),
    PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D → Nat.card D = 4 → False

namespace PairFacts

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ} {H : MData G L M n}
  {P B D : Subgroup G}

theorem relIndex_Q_eq (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    D.relIndex (QM L M) = 8 := by
  obtain ⟨-, hD4, -⟩ := hP.step610 hBLQ
  have hPQ := hP.step67 hBLQ
  have hDPB : D.relIndex P = D.relIndex B := by
    have h1 := PairFacts.relIndex_mul_card_of_le hP.D_le_P
    have h2 := PairFacts.relIndex_mul_card_of_le hP.D_le_B
    rw [hP.card_PB, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [← Subgroup.relIndex_mul_relIndex D P (QM L M) hP.D_le_P hP.P_le_Q, hDPB, hD4, hPQ]

theorem QM_eq_blockU_of_card_two (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M)
    (hD : Nat.card D = 2) : QM L M = blockU L := by
  obtain ⟨-, -, hn⟩ := hP.step610 hBLQ
  have hq : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hQ := PairFacts.relIndex_mul_card_of_le hP.D_le_Q
  rw [hP.relIndex_Q_eq hBLQ, hD] at hQ
  have hV : Nat.card ↥(blockU L) = 16 := by
    rw [H.card_V, hq]
    norm_num
  refine (Subgroup.eq_of_le_of_card_ge H.blockU_le_QM ?_).symm
  rw [hV, ← hQ]

end PairFacts

theorem print65_of_leaves (hE1 : FooteNonsolvableSimple) (hTor : Print65Torus)
    (hD1 : Print66D1) (hG4 : Print611Gen4) (hFus : Print612) :
    ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G),
      Sit64 G L M T n D g → False := by
  intro G _ _ L M T n D g hs
  by_cases hD : D = ⊥
  · subst hD
    exact hD1 G L M T n g hs
  have hP := pairFacts_of_sit64 hE1 hs (hTor G L M T n D g hs)
  rcases hP.step66 with hBLQ | ⟨hD', -⟩
  · obtain ⟨-, -, hDcard⟩ := hP.step611 hBLQ
    rcases hDcard with h2 | h4
    · exact hG4 G L M T n D g hE1 hs hP h2
    · exact hFus G L M T n D g hE1 hs hP h4
  · exact hD hD'

end CFSG.CGT.PushingUpLit.T2KR
