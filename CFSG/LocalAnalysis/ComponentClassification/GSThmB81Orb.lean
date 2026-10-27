module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Z

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

variable {G : Type*} [Group G]

theorem mul_conj_inv_cancel (n w : G) : n * (n⁻¹ * w * n) * n⁻¹ = w := by group

theorem inv_conj_cancel (n w : G) : n⁻¹ * (n * w * n⁻¹) * n = w := by group

theorem conj_mul_distrib (n x y : G) : n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) := by
  group

theorem conj_mul_inv_right (n c w : G) :
    (n * c⁻¹)⁻¹ * w * (n * c⁻¹) = c * (n⁻¹ * w * n) * c⁻¹ := by group

theorem conj_mul_right (n c w : G) : (n * c)⁻¹ * w * (n * c) = c⁻¹ * (n⁻¹ * w * n) * c := by
  group

end Eight

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem not_conj_asigma_sigma (F : d.Facts) (h3 : ∀ c : H, c⁻¹ * d.b * c ≠ d.b * d.z) (c : H) :
    c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma := by
  intro hc
  obtain ⟨k, hk, hkz⟩ := F.z_tau
  apply h3 (h.x * d.g * c * k⁻¹)
  rw [show (h.x * d.g * c * k⁻¹)⁻¹ * d.b * (h.x * d.g * c * k⁻¹) =
      k * (c⁻¹ * ((h.x * d.g)⁻¹ * d.b * (h.x * d.g)) * c) * k⁻¹ by group, conj_b, hc,
    d.k_sigma hk hkz]

section Orbits

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

theorem conj_mem_DP {n : H} (hn : n ∈ normalizer (h.F32 : Set H)) {e : H}
    (he : e = 1 ∨ e = d.z ∨ e = h.a) : n⁻¹ * e * n ∈ h.D ⊔ h.P := by
  have hz : d.z ∈ h.D ⊔ h.P := mem_sup_left d.z_D
  have ha : h.a ∈ h.D ⊔ h.P := mem_sup_right h.toHyp52.a_mem_P
  rcases he with rfl | rfl | rfl
  · rw [mul_one, inv_mul_cancel]; exact one_mem _
  · rcases conj_z_cases hv I F hn with h1 | h1 <;> rw [h1]
    exacts [ha, hz]
  · rcases conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hn with h1 | h1 <;>
      rw [h1]
    exacts [ha, hz]

theorem conj_sigma_cases (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) {n : H}
    (hn : n ∈ normalizer (h.F32 : Set H)) :
    n⁻¹ * d.sigma * n = d.sigma ∨ n⁻¹ * d.sigma * n = h.a * d.z * d.sigma := by
  have hmem := conj_mem_ZF32 hn (sigma_mem_ZF I F)
  rw [ZF_eq I F] at hmem
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, he⟩ := mem_ZF_cases hmem
  have hninv : n⁻¹ ∈ normalizer (h.F32 : Set H) := inv_mem hn
  rcases he₂ with rfl | rfl
  · exfalso
    apply d.sigma_not_mem_DP I.cf1 I.cf2 F
    have hσ : d.sigma = (n⁻¹)⁻¹ * e₀ * n⁻¹ * ((n⁻¹)⁻¹ * e₁ * n⁻¹) := by
      rw [← Eight.conj_mul_distrib, ← mul_one (e₀ * e₁), ← he, inv_inv,
        Eight.mul_conj_inv_cancel]
    rw [hσ]
    refine mul_mem (conj_mem_DP hv I F hninv ?_) (conj_mem_DP hv I F hninv ?_)
    · rcases he₀ with rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl)]
    · rcases he₁ with rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inr rfl)]
  · rcases he₀ with rfl | rfl <;> rcases he₁ with rfl | rfl
    · left; rw [he, one_mul, one_mul]
    · exfalso
      apply h3 n⁻¹
      rw [one_mul] at he
      rw [inv_inv, ← he, Eight.mul_conj_inv_cancel]
    · exfalso
      rw [mul_one] at he
      rcases conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hn with h1 | h1
      · obtain ⟨c, hc⟩ := d.exists_conj_sigma F
        apply h3 (n * c⁻¹)
        rw [Eight.conj_mul_inv_right, Eight.conj_mul_distrib, h1, he, ← mul_assoc h.a d.z d.sigma,
          ← hc, Eight.mul_conj_inv_cancel]
      · apply h3 n
        rw [Eight.conj_mul_distrib, h1, he, ← mul_assoc d.z d.z d.sigma, d.z_mul_self, one_mul]
    · right; rw [he, d.z_comm_a]

theorem conj_asigma_cases (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) {n : H}
    (hn : n ∈ normalizer (h.F32 : Set H)) :
    n⁻¹ * (h.a * d.sigma) * n = h.a * d.sigma ∨ n⁻¹ * (h.a * d.sigma) * n = d.z * d.sigma := by
  rw [Eight.conj_mul_distrib]
  have haa := Six.a_mul_a_self h.toHyp52
  rcases conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F hn with h1 | h1 <;>
    rcases conj_sigma_cases hv I F h3 hn with h2 | h2 <;> rw [h1, h2]
  · left; rfl
  · right
    rw [mul_assoc h.a d.z d.sigma, ← mul_assoc h.a h.a (d.z * d.sigma), haa, one_mul]
  · right; rfl
  · left
    rw [mul_assoc h.a d.z d.sigma, ← mul_assoc d.z h.a (d.z * d.sigma), d.z_comm_a,
      mul_assoc h.a d.z (d.z * d.sigma), ← mul_assoc d.z d.z d.sigma, d.z_mul_self, one_mul]

theorem U_le_centralizer_asigma (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
    (h6 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.z * d.sigma) :
    h.U81 v ≤ centralizer ({h.a * d.sigma} : Set H) := by
  intro u hu
  rw [mem_centralizer_singleton_iff]
  rcases conj_asigma_cases hv I F h3 (U_le_normalizer_F hv hu) with h1 | h1
  · calc u * (h.a * d.sigma) = u * (u⁻¹ * (h.a * d.sigma) * u) := by rw [h1]
      _ = h.a * d.sigma * u := by group
  · exact absurd h1 (h6 u)

theorem exists_sylow_le_centralizer_B (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
    (h6 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.z * d.sigma) :
    ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H) := by
  obtain ⟨T₀, hT₀⟩ := isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
  have hU := U_le_centralizer_asigma hv I F h3 h6
  set c := h.x * d.g with hc
  refine ⟨c • T₀, fun t ht => ?_⟩
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at ht
  have ht' : c⁻¹ * t * c ∈ h.U81 v := by
    rw [← hT₀]
    convert ht using 1
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  have h1 := mem_centralizer_singleton_iff.mp (hU ht')
  rw [← conj_b] at h1
  have htb : t * d.b = d.b * t := by
    have h2 : c⁻¹ * (t * d.b) * c = c⁻¹ * (d.b * t) * c := by
      calc c⁻¹ * (t * d.b) * c = c⁻¹ * t * c * (c⁻¹ * d.b * c) := by group
        _ = c⁻¹ * d.b * c * (c⁻¹ * t * c) := h1
        _ = c⁻¹ * (d.b * t) * c := by group
    have h3 := congrArg (fun w => c * w * c⁻¹) h2
    simpa [mul_assoc] using h3
  rw [d.B_eq, mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.zpow_left (show Commute d.b t from htb.symm) k).eq)

theorem not_conj_a_b (c : H) : c⁻¹ * h.a * c ≠ d.b := by
  intro hc
  have h1 : (c * (h.x * d.g))⁻¹ * h.a * (c * (h.x * d.g)) = h.a * d.sigma := by
    rw [show (c * (h.x * d.g))⁻¹ * h.a * (c * (h.x * d.g)) =
      (h.x * d.g)⁻¹ * (c⁻¹ * h.a * c) * (h.x * d.g) by group, hc, conj_b]
  have hmem : (c * (h.x * d.g))⁻¹ * h.a * (c * (h.x * d.g)) ∈ h.ZF32 := by
    rw [h1]; exact mul_mem (a_mem_ZF I F) (sigma_mem_ZF I F)
  apply d.sigma_not_mem_DP I.cf1 I.cf2 F
  rcases conj_a_of_mem_ZF hv I F hmem with h2 | h2 <;> rw [h1] at h2
  · have : d.sigma = 1 := by
      calc d.sigma = h.a * (h.a * d.sigma) := by
            rw [← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]
        _ = 1 := by rw [h2, Six.a_mul_a_self h.toHyp52]
    rw [this]; exact one_mem _
  · have : d.sigma = h.a * d.z := by
      calc d.sigma = h.a * (h.a * d.sigma) := by
            rw [← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]
        _ = h.a * d.z := by rw [h2]
    rw [this]
    exact mul_mem (mem_sup_right h.toHyp52.a_mem_P) (mem_sup_left d.z_D)

theorem not_conj_az_b (c : H) : c⁻¹ * (h.a * d.z) * c ≠ d.b := by
  intro hc
  have h1 : (c * (h.x * d.g))⁻¹ * (h.a * d.z) * (c * (h.x * d.g)) = h.a * d.sigma := by
    rw [show (c * (h.x * d.g))⁻¹ * (h.a * d.z) * (c * (h.x * d.g)) =
      (h.x * d.g)⁻¹ * (c⁻¹ * (h.a * d.z) * c) * (h.x * d.g) by group, hc, conj_b]
  have hmem : (c * (h.x * d.g))⁻¹ * (h.a * d.z) * (c * (h.x * d.g)) ∈ h.ZF32 := by
    rw [h1]; exact mul_mem (a_mem_ZF I F) (sigma_mem_ZF I F)
  have h2 := conj_az_of_mem_ZF hv I F hmem
  rw [h1] at h2
  apply d.sigma_not_mem_DP I.cf1 I.cf2 F
  have : d.sigma = d.z := by
    calc d.sigma = h.a * (h.a * d.sigma) := by
          rw [← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]
      _ = d.z := by rw [h2, ← mul_assoc, Six.a_mul_a_self h.toHyp52, one_mul]
  rw [this]
  exact mem_sup_left d.z_D

end Orbits

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
