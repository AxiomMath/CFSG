module

public import CFSG.CGT.Stroth77.L4Sylow.EmbedSU
public import CFSG.CGT.Stroth77.L4Sylow.Sylow
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem factorization_ordSU_four {q : ℕ} (hq : q % 4 = 3) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 2 =
      3 * (q + 1).factorization 2 + 3 := by
  obtain ⟨u, hu, hqu⟩ :=
    CFSG.BrauerLinearThree.exists_odd_eq_two_pow_factorization_mul (n := q + 1) (by omega)
  set n := (q + 1).factorization 2
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have key : q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) =
      2 ^ 3 * (q + 1) ^ 3 *
        (q ^ 6 * (2 * t + 1) ^ 2 * (16 * t ^ 2 + 20 * t + 7) * (8 * t ^ 2 + 12 * t + 5)) := by
    zify [h2, h4]
    rw [ht]
    push_cast
    ring
  have hodd : Odd (u ^ 3 * (q ^ 6 * (2 * t + 1) ^ 2 * (16 * t ^ 2 + 20 * t + 7) *
      (8 * t ^ 2 + 12 * t + 5))) := by
    have hq' : Odd q := Nat.odd_iff.2 (by omega)
    refine hu.pow.mul (((hq'.pow.mul (odd_two_mul_add_one t).pow).mul ?_).mul ?_)
    · exact ⟨8 * t ^ 2 + 10 * t + 3, by ring⟩
    · exact ⟨4 * t ^ 2 + 6 * t + 2, by ring⟩
  have hform : q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) =
      2 ^ (3 * n + 3) * (u ^ 3 *
        (q ^ 6 * (2 * t + 1) ^ 2 * (16 * t ^ 2 + 20 * t + 7) * (8 * t ^ 2 + 12 * t + 5))) := by
    rw [key, hqu]
    ring
  rw [hform, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hodd.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem factorization_card_statedSU_four {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 3) :
    (Nat.card (StatedSU 4 (p ^ f) K)).factorization 2 = 3 * (p ^ f + 1).factorization 2 + 3 := by
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have := h.finite
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 4) (Fin 4) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  have h1 : (Nat.card (StatedSU 4 (p ^ f) K) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [show StatedSU 4 (p ^ f) K = unitarySU p f K 4 from rfl, unitarySU_eq_gramSU h,
      card_gramSU, hU]
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have e2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  have e4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq1
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    simp
  have hcard : Nat.card (StatedSU 4 (p ^ f) K) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
    rw [hprod] at h1
    zify [e2, e4]
    rw [h1]
    norm_num
    ring
  rw [hcard, factorization_ordSU_four hq]

namespace L4Data

variable {K : Type} [Field K] {n q : ℕ} (D : L4Data K n)

@[expose] def toProjSU (hn : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) :
    L4P n →* StatedProj (StatedSU 4 q K) :=
  (QuotientGroup.mk' _).comp (D.toSU hn hq)

theorem ker_toProjSU (hn1 : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) (hn : 2 ≤ n) :
    (D.toProjSU hn1 hq).ker = Subgroup.zpowers (cL4 n) := by
  ext a
  rw [toProjSU, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_toSU,
    D.embed_mem_statedScalars_iff, mem_zpowers_cL4 hn]

end L4Data

private theorem two_le_factorization_add_one {q : ℕ} (hq : q % 4 = 3) :
    2 ≤ (q + 1).factorization 2 := by
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
  exact Nat.dvd_of_mod_eq_zero (by omega)

theorem nonempty_mulEquiv_l4Model_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 3)
    (P : Sylow 2 (StatedProj (StatedSU 4 (p ^ f) K))) :
    Nonempty (↥(P : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) ≃*
      L4Model ((p ^ f + 1).factorization 2)) := by
  have hn2 := two_le_factorization_add_one hq
  obtain ⟨D⟩ := exists_l4Data_of_card_eq_sq hK (Nat.ordProj_dvd (p ^ f + 1) 2)
  exact nonempty_sylow_quotient_mulEquiv (D.toSU (by omega) (Nat.ordProj_dvd _ _))
    (D.toSU_injective _ _) (by rw [card_L4P, factorization_card_statedSU_four hp hf hK hq])
    (D.ker_toProjSU (by omega) _ hn2) P

theorem nonempty_mulEquiv_l4Model_of_lieModel_psu {L : Type} [Group L] {p f : ℕ}
    (hq : p ^ f % 4 = 3) (hL : CFSG.Blueprint.LieModel L .PSU 4 p f) (P : Sylow 2 L) :
    Nonempty (↥(P : Subgroup L) ≃* L4Model ((p ^ f + 1).factorization 2)) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eL⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have : Finite L := Finite.of_equiv _ eL.symm.toEquiv
  let P' : Sylow 2 (StatedProj (StatedSU 4 (p ^ f) K)) :=
    P.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have eP : ↥(P : Subgroup L) ≃* ↥(P' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) :=
    ((P : Subgroup L).equivMapOfInjective eL.toMonoidHom eL.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
  obtain ⟨eM⟩ := nonempty_mulEquiv_l4Model_statedSU hp hf hK hq P'
  exact ⟨eP.trans eM⟩

end CFSG.CGT.Stroth77.L4Sylow
