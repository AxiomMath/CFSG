module

public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpClass

open Subgroup CFSG.GH74.GLS.TwoThin
open CFSG.Open (ordA)

theorem ordA_one_odd (k : ℕ) : ordA 1 (2 * k + 1) = 2 * k * (k + 1) * (2 * k + 1) := by
  have h2 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  have h3 : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]
    simp
  have h4 : (∏ i ∈ Finset.Icc 2 (1 + 1), ((2 * k + 1) ^ i - 1)) = 4 * k * (k + 1) := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, Finset.Icc_self, Finset.prod_singleton, h2]
  have h5 : (2 * k + 1) ^ (1 * (1 + 1) / 2) = 2 * k + 1 := by norm_num
  simp only [ordA, h3, h4, h5]
  have : (2 * k + 1) * (4 * k * (k + 1)) = 2 * (2 * k * (k + 1) * (2 * k + 1)) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

theorem ordA_one_ne {q n : ℕ} (hq : Odd q)
    (hn : n ∈ ({504, 5616, 6048, 7920, 29120, 58240, 95040, 190080} : Finset ℕ)) :
    ordA 1 q ≠ n := by
  obtain ⟨k, rfl⟩ := hq
  rw [ordA_one_odd]
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hk : k ≤ 35 := by
    by_contra hk
    have hk36 : 36 ≤ k := by omega
    have : 2 * 36 * (36 + 1) * (2 * 36 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by
      gcongr
    omega
  interval_cases k <;> omega

theorem card_ne_of_inU2 {S : Type} [Group S] (hU : InU2 S) (hno : ¬ IsL34Quotient S) {n : ℕ}
    (hn : n ∈ ({504, 5616, 6048, 7920, 29120, 58240, 95040, 190080} : Finset ℕ)) :
    Nat.card S ≠ n := by
  rcases hU.2 with ⟨_, _, -, -, hodd, hL⟩ | he | ⟨hL34, -⟩
  · rw [card_of_lieModel_PSL (n := 2) (by norm_num) hL]
    exact ordA_one_ne hodd hn
  · obtain ⟨e⟩ := he
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h7]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  · exact absurd hL34 hno

theorem c2_u2_fm9
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    {L : Type} [Group L] [Finite L] (hP : Gen4Comp L) (hC : InC2 L) (hU : InU2 L)
    (hno : ¬ IsL34Quotient L) : HasL2Model L IsFM9 := by
  rcases c2Shape_of_inC2 hG hF hC hP with ⟨-, hsimple⟩ | ⟨-, hc2, hM⟩ | ⟨-, hc2, hS⟩
  · rcases hsimple with ⟨p, f, hp, -, hfm, hL⟩ | hL28 | hL33 | hU33 | hSz | hM11
    · exact ⟨p, f, hp, (Generic.stated_of_lieModel_PSL hL).1.2.1, hfm, hL⟩
    · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 504) (by decide))
      rw [card_of_lieModel_PSL (by norm_num) hL28]
      decide
    · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 5616) (by decide))
      rw [card_of_lieModel_PSL (by norm_num) hL33]
      decide
    · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 6048) (by decide))
      rw [card_of_lieModel_PSU (by norm_num) (by norm_num) hU33]
      decide
    · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 29120) (by decide))
      rw [card_of_lieModel_twistedB2 hSz]
      decide
    · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 7920) (by decide))
      exact card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hM11
  · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 190080) (by decide))
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
      card_of_isSporadic_M12 hM]
    norm_num
  · refine absurd ?_ (card_ne_of_inU2 hU hno (n := 58240) (by decide))
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
      card_of_lieModel_twistedB2 hS]
    decide

theorem not_inU2_quotient_of_centre
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    {L : Type} [Group L] [Finite L] (hP : Gen4Comp L) (hC : InC2 L) (hcen : center L ≠ ⊥)
    {S : Type} [Group S] [Finite S] (hS : InU2 S) (hno : ¬ IsL34Quotient S)
    (e : S ≃* (L ⧸ center L)) : False := by
  have hcard : Nat.card S = Nat.card (L ⧸ center L) := Nat.card_congr e.toEquiv
  rcases c2Shape_of_inC2 hG hF hC hP with ⟨hz, -⟩ | ⟨-, -, hM⟩ | ⟨-, -, hSz⟩
  · exact hcen hz
  · refine card_ne_of_inU2 hS hno (n := 95040) (by decide) ?_
    rw [hcard, card_of_isSporadic_M12 hM]
    norm_num
  · refine card_ne_of_inU2 hS hno (n := 29120) (by decide) ?_
    rw [hcard, card_of_lieModel_twistedB2 hSz]
    decide

end CFSG.GH74.GLS.C3.Layer1.PumpClass
