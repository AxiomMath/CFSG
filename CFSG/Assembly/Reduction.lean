module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.KCore

public section

namespace CFSG.Assembly

abbrev GroupProp : Type 1 := ∀ (G : Type) [Group G], Prop

variable (C : GroupProp)

@[expose] def KProper (G : Type) [Group G] : Prop := KCore.KProperNonab C G

@[expose] def OddOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G

@[expose] def AbelianStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∀ a b : G, a * b = b * a) → C G

@[expose] def DisconnectedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Even (Nat.card G) → ¬ (involutionGraph G).Preconnected → C G

@[expose] def LowTwoRankStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Even (Nat.card G) → twoRank G ≤ 2 → C G

@[expose] def DichotomyStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ twoRank G → (involutionGraph G).Connected → IsComponentType G ∨ IsCharTwoType G

@[expose] def ComponentStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper C G → 3 ≤ twoRank G → IsComponentType G → C G

@[expose] def QuasithinStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper C G → IsCharTwoType G → evenRank G ≤ 2 → C G

@[expose] def RankThreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper C G → IsCharTwoType G → evenRank G = 3 → C G

@[expose] def LargeEvenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper C G → IsCharTwoType G → 4 ≤ evenRank G → C G

theorem charTwo_classification (hqt : QuasithinStatement C) (hr3 : RankThreeStatement C)
    (hle : LargeEvenStatement C) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper C G) (hchar : IsCharTwoType G) : C G := by
  rcases (show evenRank G ≤ 2 ∨ evenRank G = 3 ∨ 4 ≤ evenRank G by omega) with h | h | h
  · exact hqt G hnonab hK hchar h
  · exact hr3 G hnonab hK hchar h
  · exact hle G hnonab hK hchar h

theorem kProper_classification (hodd : OddOrderStatement) (hab : AbelianStatement C)
    (hdisc : DisconnectedStatement C) (hlow : LowTwoRankStatement C) (hdich : DichotomyStatement)
    (hcomp : ComponentStatement C) (hqt : QuasithinStatement C) (hr3 : RankThreeStatement C)
    (hle : LargeEvenStatement C) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hK : KProper C G) : C G := by
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · exact hab G hcomm
  have hnonab : ∃ a b : G, a * b ≠ b * a := by push Not at hcomm; exact hcomm
  have heven : Even (Nat.card G) := by
    by_contra h
    exact hcomm (IsSimpleGroup.comm_iff_isSolvable.2 (hodd G (Nat.not_even_iff_odd.mp h)))
  by_cases hpre : (involutionGraph G).Preconnected
  swap
  · exact hdisc G hnonab heven hpre
  rcases le_or_gt (twoRank G) 2 with hr | hr
  · exact hlow G hnonab heven hr
  have : Nonempty {t : G // orderOf t = 2} := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    exact ⟨⟨t, ht⟩⟩
  rcases hdich G hnonab hr ⟨hpre⟩ with hc | hc
  · exact hcomp G hnonab hK hr hc
  · exact charTwo_classification C hqt hr3 hle G hnonab hK hc

theorem classification (hodd : OddOrderStatement) (hab : AbelianStatement C)
    (hdisc : DisconnectedStatement C) (hlow : LowTwoRankStatement C) (hdich : DichotomyStatement)
    (hcomp : ComponentStatement C) (hqt : QuasithinStatement C) (hr3 : RankThreeStatement C)
    (hle : LargeEvenStatement C) (G : Type) [Group G] [Finite G] [IsSimpleGroup G] : C G := by
  suffices h : ∀ n, ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G = n → C G from
    h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn
    refine kProper_classification C hodd hab hdisc hlow hdich hcomp hqt hr3 hle G ?_
    intro K L hKtop _ _ hsimp _
    have hlt : Nat.card (K ⧸ L.subgroupOf K) < n := by
      calc Nat.card (K ⧸ L.subgroupOf K)
          ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
        _ < Nat.card (⊤ : Subgroup G) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hKtop)
        _ = n := by rw [Subgroup.card_top, hn]
    exact ih _ hlt (K ⧸ L.subgroupOf K) rfl

end CFSG.Assembly
