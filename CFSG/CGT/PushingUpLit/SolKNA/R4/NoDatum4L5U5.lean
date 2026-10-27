module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem noDatum4_l5Ne3 : ∀ (F : Type) [Group F], SmallL5Ne3 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h4, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD
  have : Finite F := Finite.of_equiv N eN.toEquiv
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_PSL5 hp hf h4 hm))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  obtain ⟨hodd, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hoddK : Odd (Nat.card K) := by rw [hK]; exact hodd
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨H₁, H₂, h₁, h₂, hc, he₁, he₂⟩ := exists_sl2_pair_of_psl5 hoddK (eN.trans e) ht
  exact TightDatum.not_fourGenerated_of_twoSL2Shape_cyclic4 hD hsR hsN hs4 htN hoddK
    (by rw [hK]; omega) ⟨H₁, H₂, h₁, h₂, hc, he₁, he₂⟩ hgen

theorem smallLeafR_l5Ne3 {r : ℕ} : SmallLeafR r SmallL5Ne3 :=
  SmallLeafR.of_noDatum4 noDatum4_l5Ne3

theorem noDatum4_u5 : ∀ (F : Type) [Group F], SmallU5 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD
  have hsm := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have hg : Odd (Nat.gcd 5 (p ^ f + 1)) :=
    (by decide : Odd 5).of_dvd_nat (Nat.gcd_dvd_left 5 _)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_PSU hsm hg))
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hsm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := ClassicalGroups.Unitary.charP_of_card_sq hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have := hp.two_le
    omega
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨H₁, H₂, h₁, h₂, hc, he₁, he₂⟩ := exists_sl2_pair_of_psu5 hK hp2 h5 (eN.trans e) ht
  have hq := card_fixedSubfield hK
  exact TightDatum.not_fourGenerated_of_twoSL2Shape_cyclic4 hD hsR hsN hs4 htN
    (by rw [hq]; exact hodd) (by rw [hq]; omega) ⟨H₁, H₂, h₁, h₂, hc, he₁, he₂⟩ hgen

theorem smallLeafR_u5 {r : ℕ} : SmallLeafR r SmallU5 :=
  SmallLeafR.of_noDatum4 noDatum4_u5

end CFSG.CGT.PushingUpLit.SolKNA.R4
