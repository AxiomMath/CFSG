module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx6

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem card_S_of (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ((S = S1 S K₁ ∧ Nat.card ↥S = Nat.card ↥(S1 S K₁)) ∨
      (S ≠ S1 S K₁ ∧ Nat.card ↥S = 2 * Nat.card ↥(S1 S K₁))) := by
  have hle : (S1 S K₁).relIndex S ≤ 2 := hs.fused.p66.2.1.1
  have hpos : (S1 S K₁).relIndex S ≠ 0 := Basic.relIndex_ne_zero' _ _
  have hmul := Basic.card_mul_relIndex_of_le (S1_le_S : S1 S K₁ ≤ S)
  by_cases hSS : S = S1 S K₁
  · left
    refine ⟨hSS, ?_⟩
    have h1 : (S1 S K₁).relIndex S = 1 := Subgroup.relIndex_eq_one.2 hSS.le
    rw [← hmul, h1, mul_one]
  · right
    refine ⟨hSS, ?_⟩
    have h1 : (S1 S K₁).relIndex S = 2 := by
      have hne : (S1 S K₁).relIndex S ≠ 1 := fun h' =>
        hSS (le_antisymm (Subgroup.relIndex_eq_one.1 h') S1_le_S)
      omega
    rw [← hmul, h1, mul_comm]

theorem cases8_aux (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8) :
    Nat.card ↥(Pof S K₂) = 8 ∧
      ((S = S1 S K₁ ∧ Nat.card ↥S = 2 ^ 6 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁) ∨
       (S ≠ S1 S K₁ ∧ Nat.card ↥S = 2 ^ 7 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁) ∨
       (S ≠ S1 S K₁ ∧ Nat.card ↥S = 2 ^ 8 ∧ Qof S K₁ ≠ Pof S K₂ ∧ Qof S K₂ ≠ Pof S K₁)) := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hP₂ : Nat.card ↥(Pof S K₂) = 8 := by omega
  obtain ⟨-, hcard⟩ := hs.card_S1 hII
  have hP := hs.card_P hII
  have hPz : Nat.card ↥(Pz S z) = 32 := by rw [hP8, hP₂] at hP; omega
  have hS1 : Nat.card ↥(S1 S K₁) = 64 * e := by rw [hcard, hri, hPz]; ring
  refine ⟨hP₂, ?_⟩
  rcases he with rfl | rfl
  · have hQ₁ : Qof S K₁ = Pof S K₂ :=
      (Subgroup.eq_of_le_of_card_ge (hs.P₂_le_Q₁ hII) (by rw [hq1, one_mul])).symm
    have hQ₂ : Qof S K₂ = Pof S K₁ := (hs.Q₂_eq_P₁_of_e_one hII hq2).symm
    rcases hs.card_S_of with ⟨hSS, hc⟩ | ⟨hSS, hc⟩
    · left
      exact ⟨hSS, by rw [hc, hS1]; norm_num, hQ₁, hQ₂⟩
    · right; left
      exact ⟨hSS, by rw [hc, hS1]; norm_num, hQ₁, hQ₂⟩
  · have hne₂ : Qof S K₂ ≠ Pof S K₁ := by
      intro h'
      have : Nat.card ↥(Qof S K₂) = Nat.card ↥(Pof S K₁) := by rw [h']
      omega
    have hne₁ : Qof S K₁ ≠ Pof S K₂ := by
      intro h'
      have : Nat.card ↥(Qof S K₁) = Nat.card ↥(Pof S K₂) := by rw [h']
      omega
    have hSS := hs.S_ne_S1 hII hq hrec hne₂
    rcases hs.card_S_of with ⟨hSS', -⟩ | ⟨-, hc⟩
    · exact absurd hSS' hSS
    · right; right
      exact ⟨hSS, by rw [hc, hS1]; norm_num, hne₁, hne₂⟩

end Setup8

theorem cases8 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
      Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 →
        Nat.card ↥(Pof S K₂) = 8 ∧
        ((S = S1 S K₁ ∧ Nat.card ↥S = 2 ^ 6 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁) ∨
         (S ≠ S1 S K₁ ∧ Nat.card ↥S = 2 ^ 7 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁) ∨
         (S ≠ S1 S K₁ ∧ Nat.card ↥S = 2 ^ 8 ∧ Qof S K₁ ≠ Pof S K₂ ∧ Qof S K₂ ≠ Pof S K₁)) := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs hP8
  exact hs.cases8_aux hII hq hrec hP8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
