module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open Matrix

variable {n : ℕ} {K : Type} [Field K]

abbrev pI (h : UnitaryFieldData 2 n K) : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem three_dvd_two_pow_add_one (hodd : n % 2 = 1) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, pow_mul]
  have : (2 ^ 2) ^ k % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  omega

theorem center_eq_unitaryScalars (h : UnitaryFieldData 2 n K) (hodd : n % 2 = 1) :
    Subgroup.center (unitarySU 2 n K 3) = unitaryScalars h 3 := by
  have : Finite K := h.finite
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  refine (Subgroup.eq_of_le_of_card_ge (unitaryScalars_le_center h 3) ?_).symm
  rw [CFSG.Open.StatedCenterThree.card_center_statedSU_three hK (three_dvd_two_pow_add_one hodd),
    card_unitaryScalars h (by norm_num)]
  have := three_dvd_two_pow_add_one hodd
  rw [Nat.gcd_eq_left this]

theorem exists_autHom_injective {L : Type} [Group L] (h : UnitaryFieldData 2 n K)
    (hodd : n % 2 = 1) (hn : 1 < n) (e : L ≃* ↥(StatedSU 3 (2 ^ n) K)) :
    ∃ Φ : MulAut L →* MulAut (pI h), Function.Injective Φ := by
  have : Finite K := h.finite
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (unitarySU 2 n K 3) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl (by
      intro hc
      have h2 : 2 ^ n = 2 := (Prod.mk.inj hc).2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega)
  let θ : (unitarySU 2 n K 3 ⧸ Subgroup.center (unitarySU 2 n K 3)) ≃* pI h :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_unitaryScalars h hodd)).trans
      (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3)
  refine ⟨((MulAut.congr θ).toMonoidHom.comp
    ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      (unitarySU 2 n K 3)).comp (MulAut.congr e).toMonoidHom)), ?_⟩
  exact ((MulAut.congr θ).injective.comp
    ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _).comp
      (MulAut.congr e).injective))

theorem hq_aux (h1 : 1 < n) : ¬(3 = 3 ∧ 2 ^ n = 2) := by
  rintro ⟨-, h2⟩
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem le_primeFormD_of_isPGroup_three (h : UnitaryFieldData 2 n K) (h1 : 1 < n)
    (h3 : n % 3 ≠ 0) (E : Subgroup (MulAut (pI h))) (hE : IsPGroup 3 E) :
    E ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have : Finite K := h.finite
  have hq := hq_aux h1
  rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq]
  intro e he
  rw [MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := hE ⟨e, he⟩
  have hk' : (primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq e) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : e ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hcard : Nat.card (RingAut K) = 2 * n := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hdvd1 : orderOf (primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq e) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq e) ∣ 2 * n := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (2 * n) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)

theorem not_nine_dvd_four_pow_sub_one (h3 : n % 3 ≠ 0) : ¬ 9 ∣ 4 ^ n - 1 := by
  have hpos : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hmod : 4 ^ n % 9 = 4 ∨ 4 ^ n % 9 = 7 := by
    obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 1 ∨ n = 3 * m + 2 := ⟨n / 3, by omega⟩
    have h64 : (4 ^ 3) ^ m % 9 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rcases hm with rfl | rfl
    · left
      rw [pow_add, pow_mul, Nat.mul_mod, h64]
      norm_num
    · right
      rw [pow_add, pow_mul, Nat.mul_mod, h64]
      norm_num
  omega

theorem three_pow_le_three_of_dvd {N k : ℕ} (hN : ¬ 9 ∣ N) (hk : 3 ^ k ∣ N) : 3 ^ k ≤ 3 := by
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp_all
  exact hN (Nat.dvd_trans (by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact ⟨3 ^ j, by ring⟩) hk)

theorem card_le_three_of_isPGroup_dvd {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    {N : ℕ} (hN : ¬ 9 ∣ N) (hd : Nat.card G ∣ N) : Nat.card G ≤ 3 := by
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  rw [hk] at hd ⊢
  exact three_pow_le_three_of_dvd hN hd

end CFSG.LocalAnalysis.GLTheoremA
