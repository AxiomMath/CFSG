module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerTwoGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.GorensteinWalter Subgroup
open scoped MatrixGroups

theorem gen49l2_trace_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [CharP K p]
    (A : SL(2, K)) (hA : A ^ p ∈ Subgroup.center SL(2, K)) :
    A.val 0 0 + A.val 1 1 = 2 ∨ A.val 0 0 + A.val 1 1 = -2 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r * r = 1 := by simpa [sq] using hr
  have hrp : r ^ p = r := by
    rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
    · simp
    · exact Odd.neg_one_pow ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hMp : (A.val) ^ p = Matrix.scalar (Fin 2) r := by
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    exact hrA.symm
  have hcomm : Commute A.val (Matrix.scalar (Fin 2) r) :=
    (Matrix.scalar_commute r (fun r' => Commute.all r r') A.val).symm
  have hnil : (A.val - Matrix.scalar (Fin 2) r) ^ p = 0 := by
    rw [sub_pow_char_of_commute p hcomm, hMp, ← map_pow, hrp, sub_self]
  have hdet : (A.val - Matrix.scalar (Fin 2) r).det = 0 := by
    have h := congrArg Matrix.det hnil
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h
  have hdA : A.val.det = 1 := A.property
  rw [Matrix.det_fin_two] at hdet hdA
  simp [Matrix.scalar_apply] at hdet
  have key : r * (A.val 0 0 + A.val 1 1) = 2 := by linear_combination -hdet + hdA + hr2
  have h2 : A.val 0 0 + A.val 1 1 = 2 * r := by
    calc A.val 0 0 + A.val 1 1 = (r * r) * (A.val 0 0 + A.val 1 1) := by rw [hr2, one_mul]
      _ = r * (r * (A.val 0 0 + A.val 1 1)) := by ring
      _ = 2 * r := by rw [key]; ring
  rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
  · left
    simpa using h2
  · right
    simpa using h2

private theorem gen49l2_arith {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {t k : K}
    (h₁ : t + k = 2 ∨ t + k = -2) (h₂ : t + 2 * k = 2 ∨ t + 2 * k = -2)
    (h₃ : t + 3 * k = 2 ∨ t + 3 * k = -2) : k = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 4 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h4
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃
  · linear_combination h₂ - h₁
  · linear_combination h₂ - h₁
  · exact absurd (by linear_combination (h₂ - h₁) - (h₃ - h₂)) h8
  · exact absurd (by linear_combination (h₂ - h₁) - (h₃ - h₂)) h4
  · exact absurd (by linear_combination (h₃ - h₂) - (h₂ - h₁)) h4
  · exact absurd (by linear_combination (h₃ - h₂) - (h₂ - h₁)) h8
  · linear_combination h₂ - h₁
  · linear_combination h₂ - h₁

theorem gen49l2_exists_conj {H : Type*} [Group H] {V : Subgroup H} [Finite V] {c : H}
    (hc : c ∈ normalizer (V : Set H)) (hfree : ∀ g ∈ V, g * c = c * g → g = 1) :
    ∀ v ∈ V, ∃ w ∈ V, v * c = w * c * w⁻¹ := by
  have hmem : ∀ w ∈ V, w * c * w⁻¹ * c⁻¹ ∈ V := by
    intro w hw
    have h1 : c * w⁻¹ * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hc _).mp (V.inv_mem hw)
    simpa [mul_assoc] using V.mul_mem hw h1
  let f : V → V := fun w => ⟨w * c * w⁻¹ * c⁻¹, hmem w w.2⟩
  have hinj : Function.Injective f := by
    intro w w' hww'
    have h1 : (w : H) * c * (w : H)⁻¹ * c⁻¹ = w' * c * (w' : H)⁻¹ * c⁻¹ :=
      congrArg Subtype.val hww'
    have h4 : (w : H) * c * (w : H)⁻¹ = w' * c * (w' : H)⁻¹ := by simpa using h1
    have h3 : ((w'⁻¹ * w : V) : H) * c = c * ((w'⁻¹ * w : V) : H) := by
      push_cast
      calc (w' : H)⁻¹ * w * c = (w' : H)⁻¹ * (w * c * (w : H)⁻¹) * w := by group
        _ = (w' : H)⁻¹ * (w' * c * (w' : H)⁻¹) * w := by rw [h4]
        _ = c * ((w' : H)⁻¹ * w) := by group
    have h6 : (w'⁻¹ * w : V) = 1 := Subtype.ext (hfree _ (w'⁻¹ * w).2 h3)
    exact (inv_mul_eq_one.mp h6).symm
  intro v hv
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨v, hv⟩
  refine ⟨w, w.2, ?_⟩
  have h1 : (w : H) * c * (w : H)⁻¹ * c⁻¹ = v := congrArg Subtype.val hw
  rw [← h1]
  group

theorem gen49l2_eq_one_of_mem_upper {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    {V : Subgroup (PSL2 K)} (hV : ¬ p ∣ Nat.card V) {g : PSL2 K} (hgV : g ∈ V)
    (hgU : g ∈ psl2UpperUnipotentSubgroup K) : g = 1 := by
  obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff g).1 hgU
  have h1 : orderOf (psl2Root b) ∣ p := orderOf_dvd_of_pow_eq_one (psl2Root_pow_prime b)
  have h2 : orderOf (psl2Root b) ∣ Nat.card V := by
    simpa using Subgroup.orderOf_dvd_natCard V hgV
  have hcop : Nat.Coprime p (Nat.card V) := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hV
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem gen49l2_trace_mul_root {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K p] {V : Subgroup (PSL2 K)} (hV : ¬ p ∣ Nat.card V) {b : K} (hb : b ≠ 0)
    (hN : psl2Root b ∈ normalizer (V : Set (PSL2 K))) {v : PSL2 K} (hv : v ∈ V) {A : SL(2, K)}
    (hA : psl2QuotientMap K A = v) :
    A.val 0 0 + A.val 1 1 + b * A.val 1 0 = 2 ∨ A.val 0 0 + A.val 1 1 + b * A.val 1 0 = -2 := by
  have hfree : ∀ g ∈ V, g * psl2Root b = psl2Root b * g → g = 1 := fun g hg hc =>
    gen49l2_eq_one_of_mem_upper hV hg (mem_upperUnipotent_of_commute hb hc)
  obtain ⟨w, hw, hwc⟩ := gen49l2_exists_conj hN hfree v hv
  have hpow : (v * psl2Root b) ^ p = 1 := by
    rw [hwc, conj_pow, psl2Root_pow_prime, mul_one, mul_inv_cancel]
  have hcenter : (A * sl2UpperUnipotent b) ^ p ∈ Subgroup.center SL(2, K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    have h : psl2QuotientMap K ((A * sl2UpperUnipotent b) ^ p) = 1 := by
      rw [map_pow, map_mul, hA]
      exact hpow
    exact h
  have hprod : (A * sl2UpperUnipotent b).val 0 0 + (A * sl2UpperUnipotent b).val 1 1 =
      A.val 0 0 + A.val 1 1 + b * A.val 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, sl2UpperUnipotent]
    ring
  rw [← hprod]
  exact gen49l2_trace_eq hp2 _ hcenter

theorem gen49l2_lowerLeft_eq_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] [CharP K p] {a : K} (ha : a ≠ 0) {V : Subgroup (PSL2 K)} (hV : ¬ p ∣ Nat.card V)
    (hN : psl2Root a ∈ normalizer (V : Set (PSL2 K))) {v : PSL2 K} (hv : v ∈ V) {A : SL(2, K)}
    (hA : psl2QuotientMap K A = v) : A.val 1 0 = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hn : ∀ n : ℕ, 0 < n → n < p →
      psl2Root ((n : K) * a) ∈ normalizer (V : Set (PSL2 K)) ∧ (n : K) * a ≠ 0 := by
    intro n hn0 hnp
    refine ⟨?_, mul_ne_zero ?_ ha⟩
    · have h : psl2Root ((n : K) * a) = psl2Root a ^ n := by
        rw [← psl2Root_nsmul, nsmul_eq_mul]
      rw [h]
      exact (normalizer (V : Set (PSL2 K))).pow_mem hN n
    · rw [Ne, CharP.cast_eq_zero_iff K p]
      exact Nat.not_dvd_of_pos_of_lt hn0 hnp
  have htr : ∀ n : ℕ, 0 < n → n < p →
      A.val 0 0 + A.val 1 1 + (n : K) * (a * A.val 1 0) = 2 ∨
        A.val 0 0 + A.val 1 1 + (n : K) * (a * A.val 1 0) = -2 := by
    intro n hn0 hnp
    obtain ⟨hnorm, hne⟩ := hn n hn0 hnp
    have h := gen49l2_trace_mul_root hp2 hV hne hnorm hv hA
    rwa [mul_assoc] at h
  have h2K : (2 : K) ≠ 0 := by
    have h : ((2 : ℕ) : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K p]
      exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
    simpa using h
  have h1 := htr 1 one_pos (by omega)
  have h2 := htr 2 two_pos (by omega)
  have h3 := htr 3 three_pos (by omega)
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2 h3
  have hk := gen49l2_arith h2K (t := A.val 0 0 + A.val 1 1) (k := a * A.val 1 0) h1 h2 h3
  exact (mul_eq_zero.mp hk).resolve_left ha

theorem gen49l2_root_coprime {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] [CharP K p] {a : K} (ha : a ≠ 0) {V : Subgroup (PSL2 K)} (hV : ¬ p ∣ Nat.card V)
    (hN : psl2Root a ∈ normalizer (V : Set (PSL2 K))) : V = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall V).mpr fun v hv => ?_
  obtain ⟨A, hA⟩ := psl2QuotientMap_surjective (K := K) v
  have hAb : A ∈ sl2Borel K :=
    (sl2_mem_stabilizer_infinity_iff A).2 (gen49l2_lowerLeft_eq_zero hp5 ha hV hN hv hA)
  have hconj : v * psl2Root a * v⁻¹ = psl2Root (A.val 0 0 ^ 2 * a) := by
    rw [← hA]
    have h := sl2Borel_conj_upperUnipotent hAb a
    calc psl2QuotientMap K A * psl2Root a * (psl2QuotientMap K A)⁻¹
        = psl2QuotientMap K (A * sl2UpperUnipotent a * A⁻¹) := by
          simp [psl2Root, map_mul, map_inv]
      _ = psl2Root (A.val 0 0 ^ 2 * a) := by rw [h]
  have hcommV : v * psl2Root a * v⁻¹ * (psl2Root a)⁻¹ ∈ V := by
    have h1 : psl2Root a * v⁻¹ * (psl2Root a)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp (V.inv_mem hv)
    simpa [mul_assoc] using V.mul_mem hv h1
  have hcommU : v * psl2Root a * v⁻¹ * (psl2Root a)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
    rw [hconj]
    exact Subgroup.mul_mem _ (psl2Root_mem _) (Subgroup.inv_mem _ (psl2Root_mem a))
  have h1 := gen49l2_eq_one_of_mem_upper hV hcommV hcommU
  have hcomm : v * psl2Root a = psl2Root a * v := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  exact gen49l2_eq_one_of_mem_upper hV hv (mem_upperUnipotent_of_commute ha hcomm)

end CFSG.LocalAnalysis.RankThreeTheoremC
