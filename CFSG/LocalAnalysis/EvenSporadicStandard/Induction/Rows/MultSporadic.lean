module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONMult
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Sporadic.Bridge.Co1Surj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Census CFSG.EvenSporadicStandard.Induction.Hyp

theorem card_center_dvd_of_sporadicMultipliers (hSM : SporadicMultipliers)
    {s : TauCeti.SporadicName} (hb : Nonempty (Carrier s ≃* Spor s)) {X : Type} [Group X]
    [Finite X] (hq : CFSG.IsQuasisimple X) (hX : IsSporadic (X ⧸ center X) s) :
    Nat.card (center X) ∣ sporadicMultiplierOrder s := by
  obtain ⟨e⟩ := hX
  obtain ⟨b⟩ := hb
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans b)
  rwa [hSM.1 s] at h

theorem oddMultTrivial_of_sporadicMultipliers (hSM : SporadicMultipliers)
    {s : TauCeti.SporadicName} (hb : Nonempty (Carrier s ≃* Spor s))
    (hord : sporadicMultiplierOrder s ∣ 2) : OddMultTrivial s := by
  intro L _ _ hL hodd he
  have h := (card_center_dvd_of_sporadicMultipliers hSM hb hL he).trans hord
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem oddMultTrivial_hn_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : OddMultTrivial .HN :=
  oddMultTrivial_of_sporadicMultipliers (s := .HN) hSM
    CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv (by decide)

theorem oddMultTrivial_b_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : OddMultTrivial .B :=
  oddMultTrivial_of_sporadicMultipliers (s := .B) hSM
    CFSG.Sporadic.Bridge.B.nonempty_mulEquiv (by decide)

theorem oddMultTrivial_co1_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : OddMultTrivial .Co1 :=
  oddMultTrivial_of_sporadicMultipliers (s := .Co1) hSM
    CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv (by decide)

theorem oddMultTrivial_ru_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : OddMultTrivial .Ru :=
  oddMultTrivial_of_sporadicMultipliers (s := .Ru) hSM
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv (by decide)

theorem hnMultiplierOdd_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : HNMultiplierOdd := by
  intro X _ _ hq hX
  have h := card_center_dvd_of_sporadicMultipliers (s := .HN) hSM
    CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv hq hX
  have h1 : Nat.card (center X) = 1 := Nat.dvd_one.1 (h.trans (by decide))
  rw [h1]
  exact odd_one

theorem monsterNoCover_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : MonsterNoCover := by
  intro L _ _ hL hX
  have h := card_center_dvd_of_sporadicMultipliers (s := .M) hSM
    CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv hL hX
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (h.trans (by decide)))

theorem onMultThree_of_sporadicMultipliers (hSM : SporadicMultipliers) : ONMultThree := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  have h : Nat.card (center X) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier NativeSporadic.ON) :=
    CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e : X ⧸ center X ≃* NativeSporadic.ON)
  rwa [hSM.2] at h

end CFSG.EvenSporadicStandard.Induction
