module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SUFacts
import CFSG.Adapters.CatalogueFieldBridges.UnitarySU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open

private theorem exists_pow_of_card_sq {K : Type} [Field K] [Fintype K] {q : ℕ}
    (hK : Fintype.card K = q ^ 2) : ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f ∧ (ringChar K).Prime := by
  haveI := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hq : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hp).1 hq
  refine ⟨f, ?_, hqf, hp⟩
  by_contra h0
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hqf
  have h1 : Fintype.card K = 1 := by rw [hK, hqf]; norm_num
  have := Fintype.one_lt_card (α := K)
  omega

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
private theorem natCard_statedSU_cast {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(StatedSU n (p ^ f) K) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  rw [show StatedSU n (p ^ f) K = unitarySU p f K n from rfl, unitarySU_eq_gramSU h, card_gramSU,
    hU]

private theorem eq_three_two_of_order {q m g : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m) (hg : g ∣ q + 1)
    {P : ℤ} (h : (q : ℤ) ^ (m * (m - 1) / 2) * P = 360 * g) : m = 3 ∧ q = 2 := by
  have hcop : Nat.Coprime q g := by
    refine Nat.Coprime.coprime_dvd_right hg ?_
    simp
  have hcopZ : IsCoprime ((q : ℤ) ^ (m * (m - 1) / 2)) (g : ℤ) :=
    (Nat.isCoprime_iff_coprime.2 hcop).pow_left
  have hdvdZ : ((q : ℤ) ^ (m * (m - 1) / 2)) ∣ 360 :=
    hcopZ.dvd_of_dvd_mul_right (Dvd.intro _ h)
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 360 := by
    exact_mod_cast hdvdZ
  have hk : 3 ≤ m * (m - 1) / 2 := by
    have : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have h3 : q ^ 3 ∣ 360 := (pow_dvd_pow q hk).trans hdvd
  have hq7 : q ≤ 7 := by
    by_contra hcon
    have h8 : 8 ≤ q := by omega
    have h1 : 8 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h8 3
    have h2 : q ^ 3 ≤ 360 := Nat.le_of_dvd (by norm_num) h3
    omega
  have hq2 : q = 2 := by
    interval_cases q <;> first | rfl | (exfalso; revert h3; decide)
  subst hq2
  have hk3 : m * (m - 1) / 2 ≤ 3 := by
    by_contra hcon
    have h4 : 2 ^ 4 ∣ 360 := (pow_dvd_pow 2 (by omega)).trans hdvd
    revert h4
    decide
  refine ⟨?_, rfl⟩
  by_contra hne
  have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem suAltSixFacts_holds : SUAltSixFacts := by
  intro K _ _ m q hK hm
  refine ⟨fun e => ?_⟩
  obtain ⟨f, hf, rfl, hp⟩ := exists_pow_of_card_sq hK
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hNat : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card, hK]
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData (ringChar K) f K :=
    ⟨hp, hf, by rw [hNat, ← pow_mul, mul_comm]⟩
  have h360 : Nat.card (↥(StatedSU m (ringChar K ^ f) K) ⧸
      Subgroup.center ↥(StatedSU m (ringChar K ^ f) K)) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hmul :=
    (Subgroup.center ↥(StatedSU m (ringChar K ^ f) K)).card_eq_card_quotient_mul_card_subgroup
  rw [h360] at hmul
  by_cases hmq : (m, ringChar K ^ f) = (3, 2)
  · obtain ⟨rfl, h2⟩ := Prod.mk.inj hmq
    have hform := natCard_statedSU_cast hUF (n := 3) (by norm_num)
    have h216 : (Nat.card ↥(StatedSU 3 (ringChar K ^ f) K) : ℤ) = 216 := by
      rw [hform, h2, show Finset.Icc 2 3 = {2, 3} by decide]
      norm_num
    have h216' : Nat.card ↥(StatedSU 3 (ringChar K ^ f) K) = 216 := by exact_mod_cast h216
    omega
  · have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat hm hmq
    have hZ : Nat.card (Subgroup.center ↥(StatedSU m (ringChar K ^ f) K)) =
        Nat.gcd m (ringChar K ^ f + 1) := by
      rw [hQ.2]
      exact (CFSG.LinearGroups.unitary_scalar_kernel hp hNat (by omega)).2.2
    rw [hZ] at hmul
    have hform := natCard_statedSU_cast hUF (n := m) (by omega)
    rw [hmul] at hform
    have hq : 2 ≤ ringChar K ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) _)
    obtain ⟨hm3, hq2⟩ := eq_three_two_of_order (q := ringChar K ^ f) (m := m)
      (g := Nat.gcd m (ringChar K ^ f + 1)) hq hm (Nat.gcd_dvd_right _ _)
      (P := ∏ i ∈ Finset.Icc 2 m, (((ringChar K ^ f : ℕ) : ℤ) ^ i - (-1) ^ i))
      (by push_cast at hform ⊢; linarith)
    exact hmq (by rw [hm3, hq2])

theorem suFactorFacts_holds : SUFactorFacts := by
  intro K _ _ m q hK hm hmq
  obtain ⟨q', hv, hq'p, hq'card, ⟨e⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      hK hm hmq
  obtain ⟨f, hf, rfl, hp⟩ := exists_pow_of_card_sq hK
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hNat : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card, hK]
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat hm hmq
  refine ⟨hQ.1.1.commutator_eq_top, ?_, fun ⟨e⟩ _ => (suAltSixFacts_holds K m _ hK hm).false e⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  refine Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedA r q', hv⟩, ?_, ⟨e⟩⟩
  show (TauCeti.LieTypeIndex.twistedA r q').characteristic = ringChar K
  rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq'p]

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
