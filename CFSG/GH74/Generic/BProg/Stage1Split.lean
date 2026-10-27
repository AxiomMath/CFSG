module

public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.BProg.Sig32

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def Stage1Nontriv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) → ∀ A : Subgroup G, IsSource2 x K A →
      ¬ IsAllowable x K A → thetaHalfPrime A ≠ ⊥

@[expose] def Stage1BalFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → P (↥K ⧸ pPrimeCore 2 ↥K) → ∀ A : Subgroup G, IsSource2 x K A →
      ¬ IsAllowable x K A → thetaHalfPrime A ≠ ⊥ → IsBal32 A

@[expose] def Stage1Bal : Prop :=
  Stage1BalFor QShape1 ∧ Stage1BalFor QShape3 ∧ Stage1BalFor QShape4 ∧ Stage1BalFor QShape5

theorem isE3_of_isSource2 {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G}
    (h : IsSource2 x K A) : IsE 3 ⊤ A := by
  obtain ⟨-, hel, hcard, -⟩ := h
  have := hel
  have hr : pRank 2 ↥A = 3 := CFSG.pRank_eq_of_card_eq_pow one_lt_two (by simpa using hcard)
  exact ⟨le_top, hel, hr.ge⟩

theorem qShapeNS_of_isSource2 {G : Type} [Group G] {x : G} {K A : Subgroup G}
    (h : IsSource2 x K A) : QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) := by
  obtain ⟨-, -, -, hcase⟩ := h
  rcases hcase with ⟨-, h⟩ | ⟨E, -, -, -, -, -, h | h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem stage1AltFor_of_parts {P : ∀ (Kt : Type) [Group Kt], Prop} (hN : Stage1Nontriv)
    (hB : Stage1BalFor P) : Stage1AltFor P := by
  intro G _ _ hyp noAlt x K hcirc hP A hsrc
  by_cases hall : IsAllowable x K A
  · exact Or.inl hall
  · right
    have hnt : thetaHalfPrime A ≠ ⊥ := hN G hyp noAlt x K hcirc (qShapeNS_of_isSource2 hsrc) A hsrc hall
    have hbal : IsBal32 A := hB G hyp noAlt x K hcirc hP A hsrc hall hnt
    have hA3 : IsE 3 ⊤ A := isE3_of_isSource2 hsrc
    exact ⟨hbal,
      (thetaHalf_one_ne_bot_iff_thetaHalfPrime_ne_bot hA3 hbal.1 hbal.2).2 hnt,
      b_ig_21_6_three_halves G A hA3 hbal.2⟩

theorem stage1Alt_of_parts (hN : Stage1Nontriv) (hB : Stage1Bal) : Stage1Alt :=
  ⟨stage1AltFor_of_parts hN hB.1, stage1AltFor_of_parts hN hB.2.1,
    stage1AltFor_of_parts hN hB.2.2.1, stage1AltFor_of_parts hN hB.2.2.2⟩

end CFSG.GH74.Generic.BProg
