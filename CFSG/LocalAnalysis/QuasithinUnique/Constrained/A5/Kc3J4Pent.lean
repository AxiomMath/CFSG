module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadX0Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Small

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem conj_pow_mem_of_mem_normalizer {Y : Type*} [Group Y] {V : Subgroup Y} {y v : Y}
    (hy : y ∈ Subgroup.normalizer (V : Set Y)) (hv : v ∈ V) (i : ℕ) :
    y ^ i * v * (y ^ i)⁻¹ ∈ V := by
  induction i with
  | zero => simpa using hv
  | succ i ih =>
    have := (Subgroup.mem_normalizer_iff.1 hy _).1 ih
    have e : y * (y ^ i * v * (y ^ i)⁻¹) * y⁻¹ = y ^ (i + 1) * v * (y ^ (i + 1))⁻¹ := by
      rw [pow_succ']
      group
    rwa [e] at this

theorem conj_pow_succ {Y : Type*} [Group Y] (y v : Y) (i : ℕ) :
    y * (y ^ i * v * (y ^ i)⁻¹) * y⁻¹ = y ^ (i + 1) * v * (y ^ (i + 1))⁻¹ := by
  rw [pow_succ']
  group

theorem fpfV_pentagon_prod {Y : Type*} [Group Y] {V : Subgroup Y} {y : Y}
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hy : y ∈ Subgroup.normalizer (V : Set Y))
    (hy5 : y ^ 5 = 1) (hfpf : ∀ v ∈ V, y * v = v * y → v = 1) {v : Y} (hv : v ∈ V) :
    v * (y * v * y⁻¹) * (y ^ 2 * v * (y ^ 2)⁻¹) * (y ^ 3 * v * (y ^ 3)⁻¹) *
      (y ^ 4 * v * (y ^ 4)⁻¹) = 1 := by
  have h1 := conj_pow_mem_of_mem_normalizer hy hv 1
  have h2 := conj_pow_mem_of_mem_normalizer hy hv 2
  have h3 := conj_pow_mem_of_mem_normalizer hy hv 3
  have h4 := conj_pow_mem_of_mem_normalizer hy hv 4
  rw [pow_one] at h1
  set p := v * (y * v * y⁻¹) * (y ^ 2 * v * (y ^ 2)⁻¹) * (y ^ 3 * v * (y ^ 3)⁻¹) *
    (y ^ 4 * v * (y ^ 4)⁻¹) with hp
  have hpV : p ∈ V :=
    V.mul_mem (V.mul_mem (V.mul_mem (V.mul_mem hv h1) h2) h3) h4
  have hy5' : y ^ 5 * v * (y ^ 5)⁻¹ = v := by rw [hy5]; group
  have hconj : y * p * y⁻¹ = (y * v * y⁻¹) * (y ^ 2 * v * (y ^ 2)⁻¹) * (y ^ 3 * v * (y ^ 3)⁻¹) *
      (y ^ 4 * v * (y ^ 4)⁻¹) * v := by
    have e : y * p * y⁻¹ = (y * v * y⁻¹) * (y * (y * v * y⁻¹) * y⁻¹) *
        (y * (y ^ 2 * v * (y ^ 2)⁻¹) * y⁻¹) * (y * (y ^ 3 * v * (y ^ 3)⁻¹) * y⁻¹) *
        (y * (y ^ 4 * v * (y ^ 4)⁻¹) * y⁻¹) := by
      rw [hp]
      group
    rw [e]
    have a2 : y * (y * v * y⁻¹) * y⁻¹ = y ^ 2 * v * (y ^ 2)⁻¹ := by
      simpa using conj_pow_succ y v 1
    have a3 : y * (y ^ 2 * v * (y ^ 2)⁻¹) * y⁻¹ = y ^ 3 * v * (y ^ 3)⁻¹ :=
      conj_pow_succ y v 2
    have a4 : y * (y ^ 3 * v * (y ^ 3)⁻¹) * y⁻¹ = y ^ 4 * v * (y ^ 4)⁻¹ :=
      conj_pow_succ y v 3
    have a5 : y * (y ^ 4 * v * (y ^ 4)⁻¹) * y⁻¹ = v := by
      rw [conj_pow_succ y v 4]
      exact hy5'
    rw [a2, a3, a4, a5]
  have hcomm : y * p * y⁻¹ = p := by
    rw [hconj, hp]
    have hm : ∀ a b : Y, a ∈ V → b ∈ V → a * b = b * a := fun a b ha hb => hab a ha b hb
    set c1 := y * v * y⁻¹
    set c2 := y ^ 2 * v * (y ^ 2)⁻¹
    set c3 := y ^ 3 * v * (y ^ 3)⁻¹
    set c4 := y ^ 4 * v * (y ^ 4)⁻¹
    have hc : c1 * c2 * c3 * c4 * v = v * (c1 * c2 * c3 * c4) := by
      exact hm _ _ (V.mul_mem (V.mul_mem (V.mul_mem h1 h2) h3) h4) hv
    calc c1 * c2 * c3 * c4 * v = v * (c1 * c2 * c3 * c4) := hc
      _ = v * c1 * c2 * c3 * c4 := by group
  have hyp : y * p = p * y := by
    have := congrArg (· * y) hcomm
    simpa [mul_assoc] using this
  exact hfpf p hpV hyp

theorem fpfV_closure_pentagon {Y : Type} [Group Y] [Finite Y] {V : Subgroup Y} {y : Y}
    (hcard : Nat.card V = 16) (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hy : y ∈ Subgroup.normalizer (V : Set Y)) (hy5 : orderOf y = 5)
    (hfpf : ∀ v ∈ V, y * v = v * y → v = 1) {v : Y} (hv : v ∈ V) (hv1 : v ≠ 1) :
    Subgroup.closure {v, y * v * y⁻¹, y ^ 2 * v * (y ^ 2)⁻¹, y ^ 3 * v * (y ^ 3)⁻¹} = V := by
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hprod := fpfV_pentagon_prod hab hy hy5' hfpf hv
  have h1 := conj_pow_mem_of_mem_normalizer hy hv 1
  have h2 := conj_pow_mem_of_mem_normalizer hy hv 2
  have h3 := conj_pow_mem_of_mem_normalizer hy hv 3
  have h4 := conj_pow_mem_of_mem_normalizer hy hv 4
  rw [pow_one] at h1
  set c1 := y * v * y⁻¹ with hc1
  set c2 := y ^ 2 * v * (y ^ 2)⁻¹ with hc2
  set c3 := y ^ 3 * v * (y ^ 3)⁻¹ with hc3
  set c4 := y ^ 4 * v * (y ^ 4)⁻¹ with hc4
  set W : Subgroup Y := Subgroup.closure {v, c1, c2, c3} with hW
  have hWV : W ≤ V := by
    rw [hW, Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hv
    · exact h1
    · exact h2
    · exact h3
  have hvW : v ∈ W := Subgroup.subset_closure (by simp)
  have hc1W : c1 ∈ W := Subgroup.subset_closure (by simp)
  have hc2W : c2 ∈ W := Subgroup.subset_closure (by simp)
  have hc3W : c3 ∈ W := Subgroup.subset_closure (by simp)
  have hc4W : c4 ∈ W := by
    have : c4 = (v * c1 * c2 * c3)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc (c4) * (v * c1 * c2 * c3) = (v * c1 * c2 * c3) * c4 := by
            have hm := hab c4 h4 (v * c1 * c2 * c3)
              (V.mul_mem (V.mul_mem (V.mul_mem hv h1) h2) h3)
            exact hm
        _ = 1 := hprod
    rw [this]
    exact W.inv_mem (W.mul_mem (W.mul_mem (W.mul_mem hvW hc1W) hc2W) hc3W)
  have hyW1 : ∀ a ∈ W, y * a * y⁻¹ ∈ W := by
    intro a ha
    have hmap : W.map (cm y) ≤ W := by
      rw [Subgroup.map_le_iff_le_comap, hW, Subgroup.closure_le]
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      show cm y b ∈ W
      rw [cm_apply]
      rcases hb with rfl | rfl | rfl | rfl
      · exact hc1W
      · have : y * (y * v * y⁻¹) * y⁻¹ = c2 := by
          rw [hc2]
          simpa using conj_pow_succ y v 1
        rw [this]
        exact hc2W
      · have : y * (y ^ 2 * v * (y ^ 2)⁻¹) * y⁻¹ = c3 := by
          rw [hc3]
          exact conj_pow_succ y v 2
        rw [this]
        exact hc3W
      · have : y * (y ^ 3 * v * (y ^ 3)⁻¹) * y⁻¹ = c4 := by
          rw [hc4]
          exact conj_pow_succ y v 3
        rw [this]
        exact hc4W
    exact hmap ⟨a, ha, rfl⟩
  have hmapW : W.map (cm y) ≤ W := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact hyW1 a ha
  have hmapEq : W.map (cm y) = W := by
    refine Subgroup.eq_of_le_of_card_ge hmapW ?_
    rw [Subgroup.card_map_of_injective (cm_injective y)]
  have hyN : y ∈ Subgroup.normalizer (W : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hyW1 a, fun ha => ?_⟩
    rw [← hmapEq] at ha
    obtain ⟨w, hw, hwa⟩ := ha
    have : w = a := cm_injective y (by simpa [cm_apply] using hwa)
    rw [← this]
    exact hw
  by_contra hne
  have hWlt : W < V := lt_of_le_of_ne hWV hne
  have hWcard : Nat.card W ≤ 8 := by
    have hdvd : Nat.card W ∣ Nat.card V := Subgroup.card_dvd_of_le hWV
    rw [hcard] at hdvd
    obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card W ∣ 2 ^ 4 by
      simpa using hdvd)
    by_contra hbig
    have hj4 : j = 4 := by
      have : 2 ^ j > 8 := by omega
      by_contra hj4
      have : j ≤ 3 := by omega
      have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have hcardeq : Nat.card W = Nat.card V := by rw [hjW, hj4, hcard]; norm_num
    exact hne (Subgroup.eq_of_le_of_card_ge hWV (by rw [hcardeq]))
  have hW2 : IsPGroup 2 W := by
    have hdvd : Nat.card W ∣ Nat.card V := Subgroup.card_dvd_of_le hWV
    rw [hcard] at hdvd
    obtain ⟨j, -, hjW⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card W ∣ 2 ^ 4 by
      simpa using hdvd)
    exact IsPGroup.of_card hjW
  have hycent := Kc3J4.pow_centralizer_of_orderOf_five hW2 hWcard hy5 hyN
  have hvcomm : y * v = v * y := (Subgroup.mem_centralizer_iff.1 hycent v hvW).symm
  exact hv1 (hfpf v hv hvcomm)

end CFSG.QuasithinUnique.A5
