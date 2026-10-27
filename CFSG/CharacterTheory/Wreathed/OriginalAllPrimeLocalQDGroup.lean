module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.QuasiDihedralFusion

section IndexTwo

variable {K : Type*} [Group K] [Finite K] {G : Type*} [Group G] [Finite G]

theorem exists_index_two_of_relIndex_two {B C : Subgroup K} (hB : B.Normal) (hC : C.Normal)
    (hCB : C ≤ B) (hrel : C.relIndex B = 2) (hodd : Odd B.index) :
    ∃ X : Subgroup K, X.index = 2 := by
  let φ := QuotientGroup.mk' C
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective C
  have hker : φ.ker = C := QuotientGroup.ker_mk' C
  let B' : Subgroup (K ⧸ C) := B.map φ
  have hB' : B'.Normal := hB.map φ hφ
  have hcard : Nat.card B' = 2 := by
    have h1 := card_eq_card_map_mul_card_inf φ B
    rw [hker, inf_eq_right.mpr hCB] at h1
    have h2 := Subgroup.relIndex_mul_card C B
    rw [inf_eq_left.mpr hCB] at h2
    have hCpos : 0 < Nat.card C := Nat.card_pos
    rw [hrel] at h2
    have h3 : Nat.card B' * Nat.card C = 2 * Nat.card C := by
      rw [← h1, ← h2]
    exact Nat.eq_of_mul_eq_mul_right hCpos h3
  have hindex : B'.index = B.index := by
    rw [← Subgroup.index_comap_of_surjective B' hφ, Subgroup.comap_map_eq, hker,
      sup_eq_left.mpr hCB]
  have hcop : (Nat.card B').Coprime B'.index := by
    rw [hcard, hindex]
    exact Nat.coprime_two_left.mpr hodd
  obtain ⟨X', hX'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨X'.comap φ, ?_⟩
  rw [Subgroup.index_comap_of_surjective X' hφ, hX'.index_eq_card, hcard]

theorem exists_index_two_of_relIndex_two' {K B C : Subgroup G} (hBK : B ≤ K) (hCB : C ≤ B)
    (hB : K ≤ Subgroup.normalizer (B : Set G)) (hC : K ≤ Subgroup.normalizer (C : Set G))
    (hrel : C.relIndex B = 2) (hodd : Odd (B.relIndex K)) : ∃ X : Subgroup K, X.index = 2 :=
  exists_index_two_of_relIndex_two
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hB)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCB.trans hBK)).mpr hC)
    (Subgroup.comap_mono hCB) (by rw [Subgroup.relIndex_subgroupOf hBK]; exact hrel) hodd

end IndexTwo

theorem characteristic_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {C : Subgroup X} (hC : C.Characteristic) : (C.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at hC ⊢
  intro ϕ
  have h := hC ((e.trans ϕ).trans e.symm)
  calc (C.map e.toMonoidHom).map ϕ.toMonoidHom
      = (C.map ((e.trans ϕ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
    _ = C.map e.toMonoidHom := by rw [h]

section Quaternion

variable {G : Type*} [Group G]

theorem pow_le_card_of_isMaximalQuaternionIn {R Y : Subgroup G} (h : IsMaximalQuaternionIn R Y)
    {n : ℕ} (hR : 2 ^ (2 * n + 1) ≤ Nat.card R) : 2 ^ (n + 1) ≤ Nat.card Y := by
  obtain ⟨hYR, hcases⟩ := h
  have hY : Nat.card Y = Nat.card (Y.subgroupOf R) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYR).toEquiv).symm
  rcases hcases with ⟨k, hk, ι, hι, himg⟩ | ⟨k, hk, ι, hι, himg⟩
  · have : Finite (CFSG.Open.SemidihedralGroup k) := Nat.finite_of_card_ne_zero (by
      rw [CFSG.Semidihedral.card k (by omega)]
      positivity)
    have hle : Nat.card R ≤ 2 ^ k := by
      rw [← CFSG.Semidihedral.card k (by omega)]
      exact Nat.card_le_card_of_injective ι hι
    have hYcard : Nat.card Y = 2 ^ (k - 1) := by
      rw [hY, ← Subgroup.card_map_of_injective hι, himg,
        CFSG.Semidihedral.quaternionSubgroup_card k hk, CFSG.Semidihedral.modulus]
    have hk' : 2 * n + 1 ≤ k :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp (hR.trans hle)
    rw [hYcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hstr := wreath_center_involution_and_quaternion_coordinates k hk
    have hle : Nat.card R ≤ 2 ^ (2 * k + 1) := by
      have h1 := Nat.card_le_card_of_injective ι hι
      rw [hstr.card] at h1
      calc Nat.card R ≤ 2 * (2 ^ k) ^ 2 := h1
        _ = 2 ^ (2 * k + 1) := by ring
    have hYcard : Nat.card Y = 2 ^ (k + 1) := by
      rw [hY, ← Subgroup.card_map_of_injective hι, himg, hstr.quaternion_card]
      ring
    have hk' : 2 * n + 1 ≤ 2 * k + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp (hR.trans hle)
    rw [hYcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Quaternion

section Arithmetic

theorem padicValNat_two_eq_one_of_mod_four {c : ℕ} (hc : c % 4 = 2) : padicValNat 2 c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
  have hdodd : ¬ 2 ∣ d := by omega
  rw [hd, padicValNat.mul (by norm_num) (by omega), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd hdodd]

theorem not_four_mul_dvd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) {ε : ℤ}
    (hε : ε = if q % 4 = 1 then 1 else -1) {m : ℕ} (hm : m = 2 ^ padicValInt 2 ((q : ℤ) - ε)) :
    ¬ 4 * m ∣ q * (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, c, hqa, hc4, hprod, ha0⟩ : ∃ a c : ℕ, (q : ℤ) - ε = a ∧ c % 4 = 2 ∧
      q ^ 2 - 1 = a * c ∧ a ≠ 0 := by
    obtain ⟨k, hk⟩ := hq
    have hq1 : 1 ≤ q := by omega
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    by_cases h4 : q % 4 = 1
    · simp only [h4, ↓reduceIte] at hε
      refine ⟨q - 1, q + 1, ?_, by omega, ?_, by omega⟩
      · rw [hε]
        push_cast [hq1]
        ring
      · zify [hq1, hq2]
        ring
    · simp only [h4, ↓reduceIte] at hε
      refine ⟨q + 1, q - 1, ?_, by omega, ?_, by omega⟩
      · rw [hε]
        push_cast
        ring
      · zify [hq1, hq2]
        ring
  rw [hqa, padicValInt.of_nat] at hm
  have hc0 : c ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hqodd : ¬ 2 ∣ q := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hval : padicValNat 2 (q * (q ^ 2 - 1)) = padicValNat 2 a + 1 := by
    rw [hprod, padicValNat.mul hq0 (mul_ne_zero ha0 hc0), padicValNat.mul ha0 hc0,
      padicValNat.eq_zero_of_not_dvd hqodd, padicValNat_two_eq_one_of_mod_four hc4, zero_add]
  intro hdvd
  have hne : q * (q ^ 2 - 1) ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hq0 (mul_ne_zero ha0 hc0)
  apply pow_succ_padicValNat_not_dvd (p := 2) hne
  rw [hval]
  rw [hm] at hdvd
  calc 2 ^ (padicValNat 2 a + 1 + 1) = 4 * 2 ^ padicValNat 2 a := by ring
    _ ∣ q * (q ^ 2 - 1) := hdvd

end Arithmetic

end CFSG.Wreathed.OriginalAllPrime.LocalQD
