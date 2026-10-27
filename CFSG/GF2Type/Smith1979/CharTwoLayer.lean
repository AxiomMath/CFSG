module

public import CFSG.GF2Type.Smith1979.CharTwoBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open CFSG.GF2Type.Smith1979.GammaU

variable {G : Type} [Group G] [Finite G]

theorem exists_zpowers_eq_of_card_three {H : Type*} [Group H] [Finite H] (O : Subgroup H)
    (hO : Nat.card O = 3) : ∃ θ : H, θ ^ 3 = 1 ∧ θ ≠ 1 ∧ O = zpowers θ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO1 : O ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hO
    omega
  obtain ⟨θ', hθ'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO1
  have hθ1 : (θ' : H) ≠ 1 := fun h => hθ'1 (Subtype.ext h)
  have hord : orderOf (θ' : H) = 3 := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf θ' ∣ 3 := hO ▸ orderOf_dvd_natCard θ'
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hθ'1
    · exact h
  refine ⟨θ', hord ▸ pow_orderOf_eq_one _, hθ1, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr θ'.2) ?_
  rw [hO, Nat.card_zpowers, hord]

theorem charTwoFacts_of_layer (hE0card : Nat.card E0 = 9797760) {OB OA : V12 → Prop}
    {a0 w0 : V12} (hF : E0Facts E0 OB OA a0 w0) (S : Setting G) (hw : S.width = 6) {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) (E Ob : Subgroup S.Mbar) (hO : Nat.card Ob = 3)
    (hZ : (center E).map E.subtype = Ob)
    (hX : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1) (hidx : E.index ≤ 4) :
    CharTwoFacts S := by
  obtain ⟨θ, hθ3, hθ1, hObz⟩ := exists_zpowers_eq_of_card_three Ob hO
  obtain ⟨ψ, hq, -, hψE⟩ :=
    exists_isometry_map_layer_eq_E0 S hw E hθ3 hθ1 (hZ.trans hObz) hX hE0card
  refine charTwoFacts_of_model hw H C (E := E.map S.Mbar.subtype) (Subgroup.map_subtype_le E)
    ?_ hF hq hψE
  have hsub : (E.map S.Mbar.subtype).subgroupOf S.Mbar = E := by
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective S.Mbar.subtype_injective]
  rw [Subgroup.relIndex, hsub]
  exact hidx

end CFSG.GF2Type.Smith1979.IdxFour
