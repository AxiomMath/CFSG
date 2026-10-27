module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sl2Triv

public section

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Hex CFSG.OrderReductions.FrattiniAutomorphisms
  CFSG.RankThree.PartOne.FTL
open scoped commutatorElement IsMulCommutative

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem sl2_centralizes_five_three {A : Type} [Group A] [Finite A] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5) (ι : SL2 F →* A) {X : Subgroup A} (hX : IsPGroup 3 ↥X)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hle : padicValNat 3 (Nat.card ↥X) ≤ 2) :
    ∀ g, ∀ x ∈ X, ι g * x = x * ι g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : ¬ 3 ∣ Nat.card F := by rw [hF]; decide
  have : Fact (IsPGroup 3 X) := ⟨hX⟩
  by_cases hU : ∃ c : F, frattiniRepOf (p := 3) ι X hnorm (sl2U c) ≠ 1
  · exfalso
    have h1 := sl2_cross_dim_of_unip Nat.prime_three hpq (frattiniRepOf (p := 3) ι X hnorm) hU
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3)
      (V := Additive (↥X ⧸ frattini ↥X))
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive (↥X ⧸ frattini ↥X) ≃ _)] at hcard
    have hdvd : 3 ^ Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) ∣ Nat.card X :=
      hcard ▸ Subgroup.card_quotient_dvd_card (frattini ↥X)
    have h2 := (padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd
    have hdim : Module.finrank (ZMod 3) (Additive (↥X ⧸ frattini ↥X)) = 2 := by
      rw [hF] at h1
      omega
    obtain ⟨c, hc⟩ := hU
    exact hc (rep_unip_trivial_of_card_five hF hdim _ c)
  · push Not at hU
    have hL : ∀ c : F, frattiniRepOf (p := 3) ι X hnorm (sl2L c) = 1 := by
      intro c
      rw [sl2L_eq_conj, map_mul, map_mul, hU (-c), mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hpowU : ∀ c : F, sl2U c ^ Nat.card F = 1 := by
      intro c
      rw [CFSG.GH74.GLS.Stage4.Rest.sl2U_pow, card_nsmul_eq_zero', sl2U_zero]
    have hpowL : ∀ c : F, sl2L c ^ Nat.card F = 1 := by
      intro c
      rw [sl2L_pow, card_nsmul_eq_zero', sl2L_zero]
    have hmem := sl2_hom_mem ι (centralizer (X : Set A))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowU c) (hU c))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowL c) (hL c))
    intro g x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hmem g)) x hx).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
