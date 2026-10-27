module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.RankThree.PerfectCover CFSG.ComponentClassification.TBLit CFSG.GH74.Generic

theorem psp4_oddCover_of_griess (hGA : GriessMultipliersAllModels) : PSp4_oddCover := by
  intro J K _ _ _ f hf hJ hker hodd q hq hK
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ := hK
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp0⟩ : ∃ p, CharP F p := ⟨ringChar F, ringChar.charP F⟩
  obtain ⟨n, hp, hpn⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hpn
  have hq' : q = p ^ (n : ℕ) := hcard ▸ hcard'.symm ▸ rfl
  have hoddq : Odd (p ^ (n : ℕ)) := hq' ▸ hq
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Even (2 ^ (n : ℕ)) := (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
    exact (Nat.not_even_iff_odd.2 hoddq) this
  have hadm : StatedLieAdmissible .PSp 2 p n := by
    refine ⟨hp, n.pos, le_refl 2, ?_⟩
    intro h
    have : p ^ (n : ℕ) = 2 := (Prod.mk.inj h).2
    rw [this] at hoddq
    exact absurd hoddq (by decide)
  have hm : CFSG.Models.LieModel K .PSp 2 p n :=
    ⟨hadm, Or.inl ⟨hadm, F, iF, fF, hcard', ⟨e⟩⟩⟩
  have hexc : exceptionalOrders .PSp 2 p n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have h2gcd : Nat.gcd 2 (p ^ (n : ℕ) - 1) = 2 := by
    obtain ⟨k, hk⟩ := hoddq
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hcardM : Nat.card (hopfMultiplier K) = 2 := by
    rw [card_hopfMultiplier_of_griess hGA hm, hexc]
    have : genericOrders .PSp 2 p n = (2, 1) := Prod.ext h2gcd rfl
    rw [this]
    norm_num
  have hdvd := card_ker_dvd_hopfMultiplier hJ f hf hker
  rw [hcardM] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

end CFSG.GH74.GLS.Stage2.Final.Thm4
