module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.KP.SporadicRankFi22
import CFSG.Sporadic.Bridge.Fi22Surj
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Presentation.McLExact
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem card_outer_dvd_two_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card (Outer G) ≤ 2) : Nat.card (Outer G) ∣ 2 := by
  have h0 : 0 < Nat.card (Outer G) := Nat.card_pos
  obtain h1 | h2 : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2 := by omega
  · rw [h1]
    exact one_dvd 2
  · rw [h2]

theorem card_outer_dvd_two_of_card_eq {G : Type*} [Group G]
    (h : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2) : Nat.card (Outer G) ∣ 2 := by
  rcases h with h | h <;> rw [h]
  exact one_dvd 2

theorem not_dvd_card_outer_of_card_dvd_two {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Nat.card (Outer G) ∣ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer H) := by
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hd.trans h))

theorem not_dvd_card_outer_M11
    {K : Type} [Group K] (e : K ≃* TauCeti.SporadicName.M11.Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have h2 : Nat.card (Outer (NativeSporadic.Carrier .M11)) ∣ 2 :=
    card_outer_dvd_two_of_card_le_two (G := NativeSporadic.M11)
      CFSG.Sporadic.Schreier.at_m11_schreier.1
  have e' : NativeSporadic.Carrier .M11 ≃* K := b.trans e.symm
  exact not_dvd_card_outer_of_card_dvd_two e' h2 hp hp2

theorem not_dvd_card_outer_McL
    {K : Type} [Group K] (e : K ≃* TauCeti.SporadicName.McL.Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have h2 : Nat.card (Outer (NativeSporadic.Carrier .McL)) ∣ 2 :=
    card_outer_dvd_two_of_card_le_two (G := NativeSporadic.McL)
      CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  have e' : NativeSporadic.Carrier .McL ≃* K := b.trans e.symm
  exact not_dvd_card_outer_of_card_dvd_two e' h2 hp hp2

theorem not_dvd_card_outer_Fi22
    {K : Type} [Group K] (e : K ≃* TauCeti.SporadicName.Fi22.Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have h2 : Nat.card (Outer (NativeSporadic.Carrier .Fi22)) ∣ 2 :=
    card_outer_dvd_two_of_card_eq (G := NativeSporadic.Fi22)
      (.inr CFSG.RankThree.PartOne.card_outer_fi22_carrier)
  have e' : NativeSporadic.Carrier .Fi22 ≃* K := b.trans e.symm
  exact not_dvd_card_outer_of_card_dvd_two e' h2 hp hp2

theorem not_dvd_card_outer_J4
    {K : Type} [Group K] (e : K ≃* TauCeti.SporadicName.J4.Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have h2 : Nat.card (Outer (NativeSporadic.Carrier .J4)) ∣ 2 :=
    card_outer_dvd_two_of_card_eq (.inl card_outer_J4)
  have e' : NativeSporadic.Carrier .J4 ≃* K := b.trans e.symm
  exact not_dvd_card_outer_of_card_dvd_two e' h2 hp hp2

theorem card_outer_of_tits
    {K : Type} [Group K] (h : IsoLie K .tits) : Nat.card (Outer K) = 2 := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  obtain ⟨eS⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv eS,
    CFSG.Sporadic.Schreier.Tits.card_outer_titsD]

end CFSG.LocalAnalysis.RankThreeTheoremC
