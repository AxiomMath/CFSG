module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXC
public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.AS16.E2.Pump2Tables
public import CFSG.GH74.KGroups.TwoM12Fixed
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

namespace XCtx

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}

theorem pow_dvd_le (hX : XCtx X z t A T₁) (L : Subgroup X) {n : ℕ} (hn : 2 ^ n ∣ Nat.card ↥L) :
    2 ^ n ≤ 2 * Nat.card ↥T₁ ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 hn
  have hKp : IsPGroup 2 ↥K := IsPGroup.of_card hK
  have hP2 : IsPGroup 2 ↥(K.map L.subtype) :=
    hKp.of_equiv (Subgroup.equivMapOfInjective K L.subtype L.subtype_injective)
  have hPc : Nat.card ↥(K.map L.subtype) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hK]
  have := hX.bound _ hP2
  rwa [hPc] at this

theorem card_T₁_le_four (hX : XCtx X z t A T₁) (hA : Nat.card ↥A = 60) : Nat.card ↥T₁ ≤ 4 := by
  obtain ⟨k, hk⟩ := hX.T₁_pgrp.exists_card_eq
  have hdvd : Nat.card ↥T₁ ∣ 60 := hA ▸ Subgroup.card_dvd_of_le hX.T₁_le
  rw [hk] at hdvd ⊢
  have hle : 2 ^ k ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

theorem stable_2M12
    (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    (h : CFSG.GH74.E2.Shape2M12 ↥L) : False := by
  have h60 := KGroups.TwoM12.card_quasisimple_fixed_of_shape2M12 h _ (hX.conjAutL_sq hL)
    (hX.conjAutL_ne_one hL) (A.subgroupOf L) (hX.A_sub_fixed hL) (hX.A_sub_quasisimple hL.A_le)
  have hA60 : Nat.card ↥A = 60 := by
    rw [← h60]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.A_le).toEquiv).symm
  have hT := hX.card_T₁_le_four hA60
  have hLcard : Nat.card ↥L = 2 ^ 6 * 3 ^ 3 * 5 * 11 * 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
    rw [card_of_isSporadic_M12 h.2.2, h.2.1] at h1
    exact h1
  have h7 : 2 ^ 7 ∣ Nat.card ↥L := ⟨1485, by rw [hLcard]; norm_num⟩
  have h2 := hX.pow_dvd_le L h7
  have h3 : Nat.card ↥T₁ ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hT 2
  omega

theorem stable_K0
    (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    (hK0 : CFSG.GH74.E2.K0Shape ↥L) : False := by
  have h2M := (CFSG.GH74.AS16.E2.pumpUpData2).shape_of_fixed ↥L hK0 _ (hX.conjAutL_sq hL)
    (hX.conjAutL_ne_one hL) (A.subgroupOf L) (hX.A_sub_fixed hL) (hX.A_sub_quasisimple hL.A_le)
  exact hX.stable_2M12 hL h2M

theorem stable_C2
    (hG : CFSG.GH74.Generic.GenericKnownFacts) (hF : CFSG.GH74.E2.E2ComponentFacts)
    (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L) (hC : InC2 ↥L) : False := by
  have hgen : Gen4Comp ↥L := gen4Comp_of_gen4Cen
    ⟨hX.gen4, t, Subgroup.mem_center_iff.mpr hX.t_central, hX.orderOf_t⟩ L
  rcases c2Shape_of_inC2 hG hF hC hgen with ⟨-, hsimple⟩ | h2M | h2S
  · rcases hsimple with ⟨p, f, hp, hp2, hfm, hlie⟩ | hL28 | hL33 | hU33 | hSz | hM11
    · have hf1 : 1 ≤ f := (CFSG.GH74.Generic.stated_of_lieModel_PSL hlie).1.2.1
      obtain ⟨F, _, _, e0, hF0, -⟩ := IVK.Proofs2.exists_l2Field_of_hasL2Model hfm
        (⟨p, f, hp, hf1, rfl, hlie⟩ : HasL2Model ↥L (fun r => r = p ^ f))
      exact hX.stable_L2 hL hF0 e0
    · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_L28 hL28)
    · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_L33 hL33)
    · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_U33 hU33)
    · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_Sz8 hSz)
    · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_M11 hM11)
  · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_2M12 h2M)
  · exact hX.stable_K0 hL (CFSG.GH74.E2.K0Shape.of_2Sz8 h2S)

end XCtx

end CFSG.GH74.GLS.SP.Local
