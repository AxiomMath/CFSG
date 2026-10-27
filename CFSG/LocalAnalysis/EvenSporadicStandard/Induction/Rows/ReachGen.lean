module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

section Orders

theorem fi23Excl_of_card {s : TauCeti.SporadicName} {n : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = n)
    (hn : ¬ n ∣ 4089470473293004800) : Fi23Excl s := by
  intro X _ hX hXs
  have hcard : Nat.card X = 4089470473293004800 := by
    obtain ⟨e⟩ := hX
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Fi23.card_Fi23
  have hdvd : Nat.card (X ⧸ center X) ∣ Nat.card X := Subgroup.card_quotient_dvd_card (center X)
  rw [hs _ hXs, hcard] at hdvd
  exact hn hdvd

theorem notExc_of_card_group {G : Type} [Group G] {N c : ℕ} (hG : Nat.card G = N)
    (h1 : c * (c ^ 2 - 1) < 2 * N) (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1))
    (hA7 : N ≠ 2520) : NotExc G := by
  constructor
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [hG, card_alternatingGroup_seven] at h
    exact hA7 h
  · rintro ⟨p, f, hp, hp2, hm⟩
    have h := two_mul_card_of_lieModel_psl_two hp hp2 hm
    rw [hG] at h
    exact no_cubic_root N c h1 h2 (p ^ f) h.symm

theorem sporadicNotExc_of_card {s : TauCeti.SporadicName} {N c : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = N)
    (h1 : c * (c ^ 2 - 1) < 2 * N) (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1))
    (hA7 : N ≠ 2520) : SporadicNotExc s :=
  fun Y _ hY => notExc_of_card_group (hs Y hY) h1 h2 hA7

theorem oddCore_eq_bot_of_card_center_two {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (X ⧸ center X)] (hev : Even (Nat.card (X ⧸ center X)))
    (hZ : Nat.card (center X) = 2) : CFSG.oddCore X = ⊥ := by
  have hle : CFSG.oddCore X ≤ center X := oddCore_le_center_of_simple_quotient hev
  have hodd : Odd (Nat.card (CFSG.oddCore X)) := odd_card_oddCore' X
  have hdvd : Nat.card (CFSG.oddCore X) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hle
  have h1 : Nat.card (CFSG.oddCore X) = 1 := by
    obtain ⟨j, hj⟩ := hodd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact Subgroup.eq_bot_of_card_eq _ h1

noncomputable def quotientOddCoreEquiv {X : Type} [Group X] (h : CFSG.oddCore X = ⊥) :
    X ⧸ CFSG.oddCore X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

end Orders

end CFSG.EvenSporadicStandard.Induction
