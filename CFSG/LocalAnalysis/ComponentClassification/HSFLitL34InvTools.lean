module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_centralizer_of_mem_coreActionKernel {K : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x) {b : G} (hb : b ∈ coreActionKernel K) :
    b ∈ centralizer (K : Set G) := by
  set B := zpowers b with hB
  have hBK : B ≤ coreActionKernel K := zpowers_le.mpr hb
  have h1 : ⁅K, B⁆ ≤ oddIn K := by
    rw [commutator_le]
    intro k hk y hy
    have h := (mem_coreActionKernel.mp (inv_mem (hBK hy))).2 k⁻¹ (inv_mem hk)
    rw [inv_inv, inv_inv] at h
    rwa [commutatorElement_def]
  have h2 : ⁅⁅K, B⁆, K⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro x hx k hk
    rw [mem_bot, commutatorElement_def, hO x (h1 hx) k hk]
    group
  have h3 : ⁅⁅B, K⁆, K⁆ = ⊥ := by rw [commutator_comm B K, h2]
  have h4 : ⁅⁅K, K⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := B) h2 h3
  rw [hperf] at h4
  rw [mem_centralizer_iff]
  intro k hk
  have h5 : ⁅k, b⁆ ∈ ⁅K, B⁆ := commutator_mem_commutator hk (mem_zpowers b)
  rw [h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
  exact h5

theorem eq_pow_mul_self_of_odd {y : G} (hy : Odd (orderOf y)) :
    ∃ m : ℕ, y = (y * y) ^ m := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨k + 1, ?_⟩
  rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

theorem exists_decomp [Finite G] {K : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x)
    (hodd : ∀ c ∈ K, c ∈ centralizer (K : Set G) → Odd (orderOf c)) {z₀ j : G}
    (hz₀ : z₀ * z₀ = 1) (hj : j ∈ K) (hjz : j⁻¹ * z₀ ∈ coreActionKernel K)
    (hz₀K : z₀ ∉ coreActionKernel K) :
    ∃ z₁ ∈ K, z₁ * z₁ = 1 ∧ z₁ ≠ 1 ∧ z₁⁻¹ * z₀ ∈ centralizer (K : Set G) := by
  set c := j⁻¹ * z₀ with hc
  have hcC : c ∈ centralizer (K : Set G) := mem_centralizer_of_mem_coreActionKernel hperf hO hjz
  have hcj : c * j = j * c := (mem_centralizer_iff.mp hcC j hj).symm
  have hz : z₀ = j * c := by rw [hc]; group
  have hj2 : j * j = (c * c)⁻¹ := by
    have h1 : j * c * (j * c) = 1 := by rw [← hz]; exact hz₀
    have h2 : j * c * (j * c) = j * j * (c * c) := by
      rw [mul_assoc j c, ← mul_assoc c j c, hcj]; group
    rw [h2] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hj2C : j * j ∈ centralizer (K : Set G) := by
    rw [hj2]; exact inv_mem (mul_mem hcC hcC)
  have hj2odd := hodd (j * j) (mul_mem hj hj) hj2C
  set m := orderOf (j * j) with hm
  obtain ⟨k, hk⟩ := hj2odd
  have hjnot : j ∉ centralizer (K : Set G) := by
    intro hjC
    apply hz₀K
    rw [hz]
    exact mem_coreActionKernel_of_commute fun l hl =>
      (mem_centralizer_iff.mp (mul_mem hjC hcC) l hl).symm
  refine ⟨j ^ m, pow_mem hj m, ?_, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, pow_mul, pow_two, pow_orderOf_eq_one]
  · intro h1
    apply hjnot
    have e : j = (j * j) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = m + 1 by omega, pow_succ, h1, one_mul]
    rw [e]
    exact pow_mem hj2C _
  · have e : (j ^ m)⁻¹ * z₀ = ((j * j) ^ k)⁻¹ * c := by
      rw [hk, pow_succ, ← pow_two, ← pow_mul, hz]
      group
    rw [e]
    exact mul_mem (inv_mem (pow_mem hj2C k)) hcC

theorem eq_of_decomp {K : Subgroup G}
    (hodd : ∀ c ∈ K, c ∈ centralizer (K : Set G) → Odd (orderOf c)) {z₀ z₁ y : G}
    (hz₁ : z₁ ∈ K) (hy : y ∈ K) (hz₁2 : z₁ * z₁ = 1) (hy2 : y * y = 1)
    (hz₁c : z₁⁻¹ * z₀ ∈ centralizer (K : Set G)) (hyc : y⁻¹ * z₀ ∈ centralizer (K : Set G)) :
    y = z₁ := by
  set d := y⁻¹ * z₁ with hd
  have hdK : d ∈ K := mul_mem (inv_mem hy) hz₁
  have hdC : d ∈ centralizer (K : Set G) := by
    have e : d = (y⁻¹ * z₀) * (z₁⁻¹ * z₀)⁻¹ := by rw [hd]; group
    rw [e]
    exact mul_mem hyc (inv_mem hz₁c)
  have hdy : y * d = d * y := mem_centralizer_iff.mp hdC y hy
  have hd2 : d * d = 1 := by
    have e : z₁ = y * d := by rw [hd]; group
    calc d * d = (y * y) * (d * d) := by rw [hy2, one_mul]
      _ = (y * d) * (y * d) := by rw [mul_assoc y d, ← mul_assoc d y d, ← hdy]; group
      _ = 1 := by rw [← e, hz₁2]
  have hdo := hodd d hdK hdC
  have h1 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · have : d = 1 := orderOf_eq_one_iff.mp h
    rw [hd] at this
    exact (inv_mul_eq_one.mp this)
  · rw [h] at hdo
    exact absurd hdo (by decide)

theorem conj_eq_of_decomp {K : Subgroup G}
    (hodd : ∀ c ∈ K, c ∈ centralizer (K : Set G) → Odd (orderOf c)) {z₀ z₁ s : G}
    (hz₁ : z₁ ∈ K) (hz₁2 : z₁ * z₁ = 1) (hz₁c : z₁⁻¹ * z₀ ∈ centralizer (K : Set G))
    (hs : s ∈ normalizer (K : Set G)) (hsz : s * z₀ * s⁻¹ = z₀) : s * z₁ * s⁻¹ = z₁ := by
  have hyK : s * z₁ * s⁻¹ ∈ K := (mem_normalizer_iff.mp hs z₁).mp hz₁
  refine eq_of_decomp hodd hz₁ hyK hz₁2 ?_ hz₁c ?_
  · rw [show s * z₁ * s⁻¹ * (s * z₁ * s⁻¹) = s * (z₁ * z₁) * s⁻¹ by group, hz₁2]; group
  · have e : (s * z₁ * s⁻¹)⁻¹ * z₀ = s * (z₁⁻¹ * z₀) * s⁻¹ := by
      conv_lhs => rw [← hsz]
      group
    rw [e]
    exact conj_mem_centralizer hs hz₁c

theorem false_of_decomp_mul {K : Subgroup G} {t z₀ z₁ s : G}
    (houter : ∀ j ∈ K, j⁻¹ * t ∉ coreActionKernel K) (hz₁ : z₁ ∈ K)
    (hz₁c : z₁⁻¹ * z₀ ∈ centralizer (K : Set G)) (hs : s ∈ normalizer (K : Set G))
    (hsz : s * z₀ * s⁻¹ = t * z₀) : False := by
  set y := s * z₁ * s⁻¹ with hy
  have hyK : y ∈ K := (mem_normalizer_iff.mp hs z₁).mp hz₁
  have ha : y⁻¹ * (t * z₀) ∈ centralizer (K : Set G) := by
    have e : y⁻¹ * (t * z₀) = s * (z₁⁻¹ * z₀) * s⁻¹ := by rw [hy, ← hsz]; group
    rw [e]
    exact conj_mem_centralizer hs hz₁c
  set w := (y⁻¹ * (t * z₀)) * (z₁⁻¹ * z₀)⁻¹ with hw
  have hwC : w ∈ centralizer (K : Set G) := mul_mem ha (inv_mem hz₁c)
  apply houter (y * z₁⁻¹) (mul_mem hyK (inv_mem hz₁))
  have e : (y * z₁⁻¹)⁻¹ * t = z₁ * w * z₁⁻¹ := by rw [hw]; group
  have hwz : z₁ * w = w * z₁ := (mem_centralizer_iff.mp hwC z₁ hz₁)
  rw [e, hwz, mul_inv_cancel_right]
  exact mem_coreActionKernel_of_commute fun l hl => (mem_centralizer_iff.mp hwC l hl).symm

theorem not_mem_coreActionKernel_of_inverts [Finite G] {K Y : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x) (hYN : Y ≤ normalizer (K : Set G))
    (hYodd : Odd (Nat.card Y)) (hKY : ¬ ⁅K, Y⁆ ≤ oddIn K) {w : G}
    (hw : ∀ y ∈ Y, w * y * w⁻¹ = y⁻¹) : w ∉ coreActionKernel K := by
  intro hwK
  have hwC := mem_centralizer_of_mem_coreActionKernel hperf hO hwK
  apply hKY
  rw [commutator_le]
  intro k hk y hy
  have hyk : k * y = y * k := by
    have h1 : y * k * y⁻¹ ∈ K := (mem_normalizer_iff.mp (hYN hy) k).mp hk
    have hwk : w * k * w⁻¹ = k := by
      rw [← mem_centralizer_iff.mp hwC k hk]; group
    have h3 : w * (y * k * y⁻¹) * w⁻¹ = y⁻¹ * k * y := by
      calc w * (y * k * y⁻¹) * w⁻¹ = (w * y * w⁻¹) * (w * k * w⁻¹) * (w * y * w⁻¹)⁻¹ := by
            group
        _ = y⁻¹ * k * y := by rw [hw y hy, hwk, inv_inv]
    have h4 : y * k * y⁻¹ = y⁻¹ * k * y := by
      rw [← h3, ← mem_centralizer_iff.mp hwC _ h1]; group
    have h5 : (y * y) * k = k * (y * y) := by
      calc y * y * k = y * (y * k * y⁻¹) * y := by group
        _ = y * (y⁻¹ * k * y) * y := by rw [h4]
        _ = k * (y * y) := by group
    have hyo : Odd (orderOf y) := by
      have h6 := Subgroup.orderOf_dvd_natCard Y hy
      exact Odd.of_dvd_nat hYodd h6
    obtain ⟨m, hm⟩ := eq_pow_mul_self_of_odd hyo
    rw [hm]
    exact ((Commute.pow_left h5 m).eq).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hyk]
  exact one_mem _

end CFSG.ComponentClassification.HSFLit.L34Inv
