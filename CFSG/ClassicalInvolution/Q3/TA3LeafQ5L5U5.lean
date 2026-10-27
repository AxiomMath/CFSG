module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Split
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cube
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Out
public import CFSG.ClassicalInvolution.Q3.TA3SOLL5U5Uni
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

namespace Q5L5U5

theorem odd_of_pow_mod_four_eq_three {p f : ℕ} (h : p ^ f % 4 = 3) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
  · exfalso
    rw [pow_add, Nat.mul_mod] at h
    have hr : p ^ k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr' : p ^ k % 4 <;> omega
  · exact hf

theorem statedClassicalModel_of_lieModel_psl {F : Type} [Group F] {n p f : ℕ}
    (h : LieModel F .PSL n p f) : Assembly.LowTwoRank.StatedClassicalModel F .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem statedClassicalModel_of_lieModel_psu {F : Type} [Group F] {n p f : ℕ}
    (h : LieModel F .PSU n p f) : Assembly.LowTwoRank.StatedClassicalModel F .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem five_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f ≠ 3) :
    Odd (p ^ f) ∧ 5 ≤ p ^ f := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  obtain ⟨k, hk⟩ := hodd
  exact ⟨⟨k, hk⟩, by omega⟩

end Q5L5U5

theorem outTwoCyclic_PSL5 {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h4 : p ^ f % 4 = 3) (hm : LieModel X .PSL 5 p f) : Nobq.OutTwoCyclic X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Finite (LinearFlag.projectiveSL 5 K) := Finite.of_equiv X e.toEquiv
  have hfo : Odd f := Q5L5U5.odd_of_pow_mod_four_eq_three h4
  have hg : Odd (Nat.gcd 5 (p ^ f - 1)) :=
    (by decide : Odd 5).of_dvd_nat (Nat.gcd_dvd_left 5 _)
  refine Nobq.OutTwoCyclic.of_mulEquiv e (outTwoCyclic_of_card_dvd (hfo.mul hg) ?_)
  rw [← mul_assoc]
  exact higher_linear_outer_order_divides_field_gcd_bound hp hf (by norm_num) hK

theorem outTwoCyclic_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSU n p f)
    (hodd : Odd (Nat.gcd n (p ^ f + 1))) : Nobq.OutTwoCyclic X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have : Finite K := hU.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -, -, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU hC hn3 hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  refine Nobq.OutTwoCyclic.of_mulEquiv e' ?_
  set D := primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  set I := inner (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with hI
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hU.prime K hU.card).2
  refine outTwoCyclic_of_hom (primeFormFieldFactor hU hC hn3 hq) (fun _ _ => inferInstance)
    (hFker ▸ hID) ?_
  intro δ hδ k hk
  rw [hFker] at hδ
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxk : x ^ (2 ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hdvd1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ Nat.gcd n (p ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime (2 ^ k) (Nat.gcd n (p ^ f + 1)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp hx1)

theorem noQ8Datum_l5Ne3 : ∀ (F : Type) [Group F], SmallL5Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h4, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD _
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

theorem smallSimpleLeaf_l5Ne3 : SmallSimpleLeaf SmallL5Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_l5Ne3

theorem noQ8Datum_u5 : ∀ (F : Type) [Group F], SmallU5 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD _
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

theorem smallSimpleLeaf_u5 : SmallSimpleLeaf SmallU5 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_u5

end CFSG.ClassicalInvolution.Q3.TA3
