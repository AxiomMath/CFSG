module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.ConfigJ
import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup
open scoped commutatorElement

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem normC_commutator_mul_kleinV (cfg : H2Cfg G t v J) {n n' a a' : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hn' : n' ∈ centralizer ({t} : Set G))
    (ha : a ∈ kleinV t v) (ha' : a' ∈ kleinV t v) :
    ⁅n * a, n' * a'⁆ = ⁅n, n'⁆ := by
  have h1 : ⁅a, n' * a'⁆ = 1 :=
    Commute.commutator_eq
      (Commute.mul_right (cfg.kleinV_central hn' ha) (cfg.comm_of_mem ha ha'))
  have h2 : ⁅n, a'⁆ = 1 := Commute.commutator_eq (cfg.kleinV_central hn ha').symm
  calc ⁅n * a, n' * a'⁆
      = n * ⁅a, n' * a'⁆ * n⁻¹ * ⁅n, n' * a'⁆ :=
        commutatorElement_mul_left_eq_conj_mul n a (n' * a')
    _ = n * 1 * n⁻¹ * ⁅n, n' * a'⁆ := by rw [h1]
    _ = ⁅n, n' * a'⁆ := by group
    _ = ⁅n, n'⁆ * n' * ⁅n, a'⁆ * n'⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj n n' a'
    _ = ⁅n, n'⁆ * n' * 1 * n'⁻¹ := by rw [h2]
    _ = ⁅n, n'⁆ := by group

theorem commutator_mem_derived (cfg : H2Cfg G t v J) {x y : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hy : y ∈ centralizer ({t} : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ ⁅J, J⁆ := by
  obtain ⟨a, ha, j, hj, hx'⟩ := cfg.exists_mul_of_mem_centralizer hx
  obtain ⟨a', ha', j', hj', hy'⟩ := cfg.exists_mul_of_mem_centralizer hy
  have hcC : ⁅j, j'⁆ ∈ centralizer ({t} : Set G) :=
    cfg.derived_le_centralizer (commutator_mem_commutator hj hj')
  have hcac : Commute a ⁅j, j'⁆ := cfg.kleinV_central hcC ha
  have hca'c : Commute a' ⁅j, j'⁆ := cfg.kleinV_central hcC ha'
  have hay : ⁅a, a' * j'⁆ = 1 := by
    rw [← hy']
    exact Commute.commutator_eq (cfg.kleinV_central hy ha)
  have hja' : ⁅j, a'⁆ = 1 :=
    Commute.commutator_eq (cfg.kleinV_central (cfg.J_le_centralizer hj) ha').symm
  have hmain : x * y * x⁻¹ * y⁻¹ = j * j' * j⁻¹ * j'⁻¹ := by
    have h : ⁅x, y⁆ = ⁅j, j'⁆ := by
      calc ⁅x, y⁆ = ⁅a * j, a' * j'⁆ := by rw [hx', hy']
        _ = a * ⁅j, a' * j'⁆ * a⁻¹ * ⁅a, a' * j'⁆ :=
              commutatorElement_mul_left_eq_conj_mul a j (a' * j')
        _ = a * ⁅j, a' * j'⁆ * a⁻¹ * 1 := by rw [hay]
        _ = a * ⁅j, a' * j'⁆ * a⁻¹ := by rw [mul_one]
        _ = a * (⁅j, a'⁆ * a' * ⁅j, j'⁆ * a'⁻¹) * a⁻¹ := by
              rw [commutatorElement_mul_right_eq_mul_conj]
        _ = a * (1 * a' * ⁅j, j'⁆ * a'⁻¹) * a⁻¹ := by rw [hja']
        _ = a * (a' * ⁅j, j'⁆ * a'⁻¹) * a⁻¹ := by rw [one_mul]
        _ = ⁅j, j'⁆ := by rw [hca'c.mul_inv_cancel, hcac.mul_inv_cancel]
    rw [commutatorElement_def, commutatorElement_def] at h
    exact h
  rw [hmain]
  exact commutator_mem_commutator hj hj'

theorem perfect_le_derived (cfg : H2Cfg G t v J) {X : Subgroup G}
    (hX : X ≤ centralizer ({t} : Set G)) (hperf : ⁅X, X⁆ = X) : X ≤ ⁅J, J⁆ := by
  rw [← hperf]
  exact commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    commutator_mem_derived cfg (hX hg₁) (hX hg₂)

theorem mem_kleinV_of_centralizes_derived (cfg : H2Cfg G t v J) {d : G}
    (hd : d ∈ centralizer ({t} : Set G)) (h : ∀ b ∈ ⁅J, J⁆, d * b = b * d) :
    d ∈ kleinV t v := by
  obtain ⟨a, ha, j, hj, rfl⟩ := cfg.exists_mul_of_mem_centralizer hd
  have hj_cent : ∀ b ∈ ⁅J, J⁆, j * b = b * j := by
    intro b hb
    have hab : Commute a b := cfg.comm a ha b (cfg.derived_le hb)
    have hcomm_j_b : Commute j b := by
      rw [show j = a⁻¹ * (a * j) from (inv_mul_cancel_left a j).symm]
      exact (hab.inv_left).mul_left (h b hb)
    exact hcomm_j_b.eq
  rw [eq_one_of_centralizes_derived cfg hj hj_cent, mul_one]
  exact ha

theorem le_kleinV_or_derived_le (cfg : H2Cfg G t v J) {N : Subgroup G}
    (hNC : N ≤ centralizer ({t} : Set G))
    (hN : ∀ c ∈ centralizer ({t} : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) :
    N ≤ kleinV t v ∨ ⁅J, J⁆ ≤ N := by
  have hVN : kleinV t v ≤ centralizer (N : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun n hn => (cfg.kleinV_central (hNC hn) ha).symm
  let M : Subgroup G := (N ⊔ kleinV t v) ⊓ J
  have hMJ : M ≤ J := inf_le_right
  have hMnorm : ∀ j₀ ∈ J, ∀ x ∈ M, j₀ * x * j₀⁻¹ ∈ M := by
    intro j₀ hj₀ x hx
    rw [mem_inf] at hx ⊢
    obtain ⟨hxNV, hxJ⟩ := hx
    refine ⟨?_, ?_⟩
    · obtain ⟨n, hn, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hVN hxNV
      have hjn : j₀ * n * j₀⁻¹ ∈ N := hN j₀ (cfg.J_le_centralizer hj₀) n hn
      have hja : j₀ * (n * a) * j₀⁻¹ = (j₀ * n * j₀⁻¹) * a := by
        rw [show j₀ * (n * a) * j₀⁻¹ = (j₀ * n) * (a * j₀⁻¹) by group,
            (Commute.inv_right (cfg.comm a ha j₀ hj₀)).eq]
        group
      rw [hja]
      exact mul_mem_sup hjn ha
    · exact J.mul_mem (J.mul_mem hj₀ hxJ) (J.inv_mem hj₀)
  by_cases hM : M = ⊥
  · left
    intro n hn
    obtain ⟨a, ha, j, hj, hn_eq⟩ := cfg.exists_mul_of_mem_centralizer (hNC hn)
    have hj_eq : j = a⁻¹ * n := by
      rw [hn_eq, inv_mul_cancel_left]
    have hjNV : j ∈ N ⊔ kleinV t v := by
      rw [hj_eq, cfg.kleinV_central (hNC hn) ((kleinV t v).inv_mem ha)]
      exact mul_mem_sup hn ((kleinV t v).inv_mem ha)
    have hjM : j ∈ M := by
      rw [mem_inf]
      exact ⟨hjNV, hj⟩
    rw [hM, mem_bot] at hjM
    rw [hn_eq, hjM, mul_one]
    exact ha
  · right
    have hJ0M : ⁅J, J⁆ ≤ M := derived_le_of_normal cfg hMJ hMnorm hM
    have hcommN : ⁅⁅J, J⁆, ⁅J, J⁆⁆ ≤ N := by
      rw [commutator_le]
      intro x hx y hy
      have hxNV : x ∈ N ⊔ kleinV t v := (show M ≤ N ⊔ kleinV t v from inf_le_left) (hJ0M hx)
      have hyNV : y ∈ N ⊔ kleinV t v := (show M ≤ N ⊔ kleinV t v from inf_le_left) (hJ0M hy)
      obtain ⟨n, hn, a, ha, hx_eq⟩ := exists_mul_of_mem_sup_of_le_centralizer hVN hxNV
      obtain ⟨n', hn', a', ha', hy_eq⟩ := exists_mul_of_mem_sup_of_le_centralizer hVN hyNV
      have hcomm_eq : ⁅x, y⁆ = ⁅n, n'⁆ := by
        rw [hx_eq, hy_eq]
        exact normC_commutator_mul_kleinV cfg (hNC hn) (hNC hn') ha ha'
      rw [hcomm_eq]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
    simpa only [cfg.derived_perfect] using hcommN

theorem le_kleinV_of_isPGroup (cfg : H2Cfg G t v J) {N : Subgroup G}
    (hNC : N ≤ centralizer ({t} : Set G))
    (hN : ∀ c ∈ centralizer ({t} : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hp : IsPGroup 2 ↥N) :
    N ≤ kleinV t v := by
  rcases le_kleinV_or_derived_le cfg hNC hN with h | h
  · exact h
  · exact absurd (hp.to_le h) (not_isPGroup_derived cfg)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
