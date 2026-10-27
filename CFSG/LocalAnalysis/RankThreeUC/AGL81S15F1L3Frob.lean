module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
open scoped Pointwise

theorem exists_frobenius_lift {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : IsPGroup 2 N) {b c : Y ⧸ N} (hb7 : b ^ 7 = 1) (hb1 : b ≠ 1)
    (hc : c * b * c⁻¹ = b ^ 2) {y : Y} (hy : (y : Y ⧸ N) = c) :
    ∃ x y' : Y, x ^ 7 = 1 ∧ x ≠ 1 ∧ y' * x * y'⁻¹ = x ^ 2 := by
  classical
  obtain ⟨b', hb'⟩ := QuotientGroup.mk_surjective b
  have h7mem : b' ^ 7 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hb', hb7]
  obtain ⟨m, hm⟩ := hN ⟨b' ^ 7, h7mem⟩
  have hm' : (b' ^ 7) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  set x : Y := b' ^ (2 ^ m) with hx
  have hx7 : x ^ 7 = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul]
    exact hm'
  have hord : orderOf b = 7 := orderOf_eq_prime hb7 hb1
  set b₁ : Y ⧸ N := (x : Y ⧸ N) with hb₁
  have hb₁eq : b₁ = b ^ (2 ^ m) := by rw [hb₁, hx, QuotientGroup.mk_pow, hb']
  have hb₁1 : b₁ ≠ 1 := by
    intro h
    rw [hb₁eq] at h
    have h1 : orderOf b ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have : (7 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h1
    omega
  have hx1 : x ≠ 1 := by
    intro h
    apply hb₁1
    rw [hb₁, h]
    rfl
  have hcb₁ : c * b₁ * c⁻¹ = b₁ ^ 2 := by
    rw [hb₁eq, ← conj_pow, hc, ← pow_mul, ← pow_mul, mul_comm]
  have hordx : orderOf x = 7 := orderOf_eq_prime hx7 hx1
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let R : Subgroup Y := (Subgroup.zpowers b₁).comap π
  have hb₁7 : b₁ ^ 7 = 1 := by
    rw [hb₁, ← QuotientGroup.mk_pow, hx7]
    rfl
  have hordb₁ : orderOf b₁ = 7 := orderOf_eq_prime hb₁7 hb₁1
  have hxR : x ∈ R := ⟨1, by simp [π, hb₁]⟩
  have hgR : y * x * y⁻¹ ∈ R := by
    show π (y * x * y⁻¹) ∈ Subgroup.zpowers b₁
    have : π (y * x * y⁻¹) = c * b₁ * c⁻¹ := by
      simp only [π, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, hb₁]
    rw [this, hcb₁]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₁) 2
  have hNR : Nat.card R = Nat.card N * 7 := by
    have h1 : R.index = (Subgroup.zpowers b₁).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
    have h2 := Subgroup.card_mul_index R
    have h3 := Subgroup.card_mul_index (Subgroup.zpowers b₁)
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_zpowers, hordb₁] at h3
    have h5 : Nat.card R * R.index = Nat.card N * 7 * R.index := by
      rw [h2, h4, ← h3, h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) h5
  have hx7' : (y * x * y⁻¹) ^ 7 = 1 := by rw [conj_pow, hx7]; simp
  have hx1' : y * x * y⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
  have hordg : orderOf (y * x * y⁻¹) = 7 := orderOf_eq_prime hx7' hx1'
  have h2 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card R).factorization 7 = 1 := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hNR, hk, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply]
    have h2' : (2 : ℕ).factorization 7 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have h7' : (7 : ℕ).factorization 7 = 1 := Nat.Prime.factorization_self (by norm_num)
    rw [h2', h7']
    simp
  have hPcard : Nat.card ((Subgroup.zpowers x).subgroupOf R) =
      7 ^ (Nat.card R).factorization 7 := by
    have : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hordx]
    rw [hfac, pow_one, ← this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
      rw [Subgroup.zpowers_le]; exact hxR)).toEquiv
  have hQcard : Nat.card ((Subgroup.zpowers (y * x * y⁻¹)).subgroupOf R) =
      7 ^ (Nat.card R).factorization 7 := by
    have : Nat.card (Subgroup.zpowers (y * x * y⁻¹)) = 7 := by rw [Nat.card_zpowers, hordg]
    rw [hfac, pow_one, ← this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
      rw [Subgroup.zpowers_le]; exact hgR)).toEquiv
  let PR : Sylow 7 R := Sylow.ofCard _ hPcard
  let QR : Sylow 7 R := Sylow.ofCard _ hQcard
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R QR PR
  have hmem : (r : Y) * (y * x * y⁻¹) * (r : Y)⁻¹ ∈ Subgroup.zpowers x := by
    have h1 : (⟨y * x * y⁻¹, hgR⟩ : R) ∈ (QR : Subgroup R) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
    have h2 : MulAut.conj r • (⟨y * x * y⁻¹, hgR⟩ : R) ∈ MulAut.conj r • (QR : Subgroup R) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hr] at h2
    simpa [PR, Sylow.ofCard, Subgroup.mem_subgroupOf] using h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨x, r * y, hx7, hx1, ?_⟩
  have hπ : π ((r : Y) * (y * x * y⁻¹) * (r : Y)⁻¹) = b₁ ^ 2 := by
    have hrπ : π r ∈ Subgroup.zpowers b₁ := r.2
    have hcomm : Commute (π r) (b₁ ^ 2) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hrπ
      rw [← hi]
      exact ((Commute.refl b₁).zpow_left i).pow_right 2
    have : π (y * x * y⁻¹) = b₁ ^ 2 := by
      simp only [π, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
      rw [← hb₁]
      exact hcb₁
    rw [map_mul, map_mul, map_inv, this, hcomm.eq]
    simp
  have hk2 : x ^ k = x ^ 2 := by
    have h1 : b₁ ^ k = b₁ ^ 2 := by
      have := congrArg π hk
      rw [map_zpow, hπ] at this
      rw [← this]
      simp [hb₁, π]
    have h2 : (orderOf b₁ : ℤ) ∣ k - 2 := by
      rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1]
      simp
    rw [hordb₁] at h2
    have h3 : (orderOf x : ℤ) ∣ k - 2 := by rw [hordx]; exact h2
    have h4 : x ^ (k - 2) = 1 := orderOf_dvd_iff_zpow_eq_one.mp h3
    rw [zpow_sub] at h4
    simpa [mul_inv_eq_one] using h4
  have : r * y * x * (r * y)⁻¹ = (r : Y) * (y * x * y⁻¹) * (r : Y)⁻¹ := by group
  rw [this, ← hk, hk2]

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
