module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625a
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

@[expose] def B_thm1_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) →
      ∀ (x' y' : G) (K' : Subgroup G), Is2TerminalU2Triple x' y' K' → twoPartCard K' = 4

namespace Th2.L625

theorem twoPartCard_eq_of_card_kBar {G : Type} [Group G] [Finite G] (K : Subgroup G) {n : ℕ}
    (hn : (Nat.card (kBar K)).factorization 2 = n) : twoPartCard K = 2 ^ n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hne1 : Nat.card (kBar K) ≠ 0 := Nat.card_pos.ne'
  have hne2 : Nat.card (pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h2 : (Nat.card (pPrimeCore 2 ↥K)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.dvd_iff_mod_eq_zero] using hodd)
  unfold twoPartCard
  rw [h1, Nat.factorization_mul hne1 hne2, Finsupp.add_apply, h2, add_zero, hn]

theorem twoPartCard_of_l2_five {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : HasL2Model (kBar K) (fun q => q = 5)) : twoPartCard K = 4 := by
  have h60 := card_of_l2_five h
  have : (Nat.card (kBar K)).factorization 2 = 2 := by
    rw [h60]
    decide +kernel
  rw [twoPartCard_eq_of_card_kBar K this]
  norm_num

theorem lemma625b_of
    (hfour : B_thm1_four) (_h102 : B_ivk_10_2) (_hL34 : B_gen4_noL34_elem) (_h14 : B_prop14)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G}
    (hV : IsV2StarTriple x y K) (hK5 : HasL2Model (kBar K) (fun q => q = 5))
    {v w : G} {H : Subgroup G} (hU : Is2TerminalU2Triple v w H) : twoPartCard H = 4 :=
  hfour G hG x y K hV hK5 v w H hU

end Th2.L625

end CFSG.GH74.GLS
