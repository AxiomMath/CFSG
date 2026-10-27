module

public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.ClassicalInvolution.Orders.Ree
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.GH74

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordRee ordSuzuki)

theorem statedClassicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : LieModel G t n p f) : StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem chevalleyExceptionalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel G t n p f) :
    ChevalleyExceptionalModel G t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem card_of_lieModel_PSL {G : Type} [Group G] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel G .PSL n p f) : Nat.card G = ordA (n - 1) (p ^ f) := by
  obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel hn h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega),
    hK, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]

theorem card_of_lieModel_PSU {G : Type} [Group G] {n p f : ℕ} (hn : n ≠ 0) (hp2 : p ≠ 2)
    (h : LieModel G .PSU n p f) : Nat.card G = ordTwistedA (n - 1) (p ^ f) :=
  (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (statedClassicalModel_of_lieModel hn h)).2.1 rfl

theorem card_of_lieModel_PSp {G : Type} [Group G] {n p f : ℕ} (hn : n ≠ 0) (hp2 : p ≠ 2)
    (h : LieModel G .PSp n p f) : Nat.card G = ordBC n (p ^ f) :=
  (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (statedClassicalModel_of_lieModel hn h)).2.2.1 rfl

theorem card_of_lieModel_G2
    {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel G .G2 n p f) : Nat.card G = ordG2 (p ^ f) :=
  CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (t := .G2) hp2
    (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_trialityD4
    {G : Type} [Group G] {n p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel G .trialityD4 n p f) : Nat.card G = ordTrialityD4 (p ^ f) :=
  CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (t := .trialityD4) hp2
    (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_twistedG2
    {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .twistedG2 0 3 f) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card G = ordRee (3 ^ (2 * k + 1)) := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨-, k, hk, hfk, hcard⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 h
    exact ⟨k, hk, by rw [hcard, hfk]⟩
  · exact absurd h (by decide)

theorem card_of_suzukiModel
    {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    p = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card G = ordSuzuki (2 ^ f) := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine ⟨hp, a, ha, hf, ?_⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hf, ordSuzuki]
  exact Nat.mul_right_comm _ _ _

theorem card_of_lieModel_twistedB2
    {G : Type} [Group G] (h : LieModel G .twistedB2 0 2 3) :
    Nat.card G = ordSuzuki 8 := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨-, -, -, -, hcard⟩ := card_of_suzukiModel h
    exact hcard

end CFSG.GH74
