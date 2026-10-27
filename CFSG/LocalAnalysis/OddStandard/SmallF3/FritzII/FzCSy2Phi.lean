module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316D

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t rho : G} {Z E W Q : Subgroup G}

theorem fzc_sy2_phi_inf (hs : FzCSy2Str t rho Z E W Q) :
    fzlPhi Q ⊓ E = Z ∨ fzlPhi Q ⊓ E = E := by
  have hΦW : fzlPhi Q ≤ W := fzl_phi_le_of_elem hs.Q_comm hs.Q_sq
  have hZΦ : Z ≤ fzlPhi Q := by
    intro z hz
    obtain ⟨e, he, hez⟩ := hs.Z_sqrt z hz
    rw [← hez]
    exact fzl_sq_mem_phi (hs.WQ (hs.EW he))
  have hmapQ : Q.map (MulAut.conj rho : G →* G) ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact hs.rho_nrm_Q q hq
  have hΦrho : ∀ x ∈ fzlPhi Q, rho * x * rho⁻¹ ∈ fzlPhi Q := by
    intro x hx
    have hmem : (MulAut.conj rho : G →* G) x ∈
        (fzlPhi Q).map (MulAut.conj rho : G →* G) := Subgroup.mem_map_of_mem _ hx
    rw [fzl_phi_map (MulAut.conj rho : G →* G) Q] at hmem
    exact fzl_phi_mono hmapQ hmem
  set Y : Subgroup G := fzlPhi Q ⊓ E with hYdef
  have hZY : Z ≤ Y := fun z hz => ⟨hZΦ hz, hs.ZE hz⟩
  have hYE : Y ≤ E := inf_le_right
  have hYrho : ∀ y ∈ Y, rho * y * rho⁻¹ ∈ Y := by
    rintro y ⟨hyΦ, hyE⟩
    exact ⟨hΦrho y hyΦ, hs.rho_nrm_E y hyE⟩
  have hYfix : ∀ y ∈ Y, rho * y * rho⁻¹ = y → y = 1 := by
    rintro y ⟨hyΦ, hyE⟩ hy
    rcases hs.rho_Q y (hΦW.trans hs.WQ hyΦ) hy with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyE) hs.t_notin_E
  have hYmod : Nat.card Y % 3 = 1 := fzl_card_mod3_of_fpf hs.rho_ord hYrho hYfix
  have hcard16 : Nat.card Y ∣ 16 := by
    rw [← hs.card_E]
    exact Subgroup.card_dvd_of_le hYE
  have hcard4 : 4 ∣ Nat.card Y := by
    rw [← hs.card_Z]
    exact Subgroup.card_dvd_of_le hZY
  obtain ⟨k, hk⟩ := hcard4
  have hk4 : k ∣ 4 := by
    obtain ⟨m, hm⟩ := hcard16
    refine ⟨m, ?_⟩
    have hm' : 16 = 4 * (k * m) := by
      rw [hk] at hm
      exact hm.trans (by ring)
    have h44 : 4 * 4 = 4 * (k * m) := by rw [← hm']
    exact Nat.mul_left_cancel (by norm_num) h44
  have hk_le : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk4
  have hkpos : 0 < k := by
    have hge : 4 ≤ Nat.card Y := hs.card_Z.symm.trans_le (Subgroup.card_le_of_le hZY)
    rw [hk] at hge
    omega
  interval_cases k
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZY (by rw [hs.card_Z, hk])).symm
  · exfalso
    rw [hk] at hYmod
    omega
  · exfalso
    exact absurd hk4 (by norm_num)
  · right
    exact Subgroup.eq_of_le_of_card_ge hYE (by rw [hs.card_E, hk])

theorem fzc_sy2_phi (hs : FzCSy2Str t rho Z E W Q) (hP : t ∈ ⁅Q, zpowers rho⁆) :
    fzlPhi Q = W := by
  have hΦW : fzlPhi Q ≤ W := fzl_phi_le_of_elem hs.Q_comm hs.Q_sq
  have htΦ : t ∈ fzlPhi Q := by
    have h1 := fzl_norm_mem hs.rho_ord hs.rho_nrm_Q
      (fun a ha b hb => fzl_comm_mem_phi ha hb) (hΦW.trans hs.WQ) hP
    have h3 : rho ^ 2 * t * (rho ^ 2)⁻¹ = t := by
      calc rho ^ 2 * t * (rho ^ 2)⁻¹
          = rho * (rho * t * rho⁻¹) * rho⁻¹ := by
            rw [pow_two, mul_inv_rev]; group
        _ = t := by simp only [hs.rho_t]
    rw [hs.rho_t, h3] at h1
    have htt : t * t * t = t := by rw [← pow_two, hs.t_sq, one_mul]
    rw [htt] at h1
    exact h1
  rcases fzc_sy2_phi_inf hs with hYZ | hYE_eq
  · exfalso
    have hΦ_subset : ∀ w ∈ fzlPhi Q, w ∈ Z ∨ ∃ z ∈ Z, w = t * z := by
      intro w hw
      rcases hs.W_split w (hΦW hw) with hwE | htwE
      · left
        have hmem : w ∈ fzlPhi Q ⊓ E := ⟨hw, hwE⟩
        rwa [hYZ] at hmem
      · right
        have hmem : t * w ∈ fzlPhi Q ⊓ E := ⟨mul_mem htΦ hw, htwE⟩
        rw [hYZ] at hmem
        exact ⟨t * w, hmem, by rw [← mul_assoc, ← pow_two, hs.t_sq, one_mul]⟩
    have hQsq : ∀ q ∈ Q, q ^ 2 ∈ Z := by
      intro q hq
      by_cases hqW : q ∈ W
      · exact hs.W_sq q hqW
      · rcases hΦ_subset (q ^ 2) (fzl_sq_mem_phi hq) with hZ | ⟨z, hzZ, hz_eq⟩
        · exact hZ
        · exfalso
          have hqz : q * z * q⁻¹ = z := hs.Q_Z q hq z hzZ
          have hcomm2 : q * q ^ 2 * q⁻¹ = q ^ 2 := by rw [pow_two]; group
          have ht_eq : q * t * q⁻¹ = t := by
            have h1 : q * (t * z) * q⁻¹ = t * z := by
              rw [← hz_eq]
              exact hcomm2
            calc q * t * q⁻¹
                = (q * (t * z) * q⁻¹) * (q * z * q⁻¹)⁻¹ := by group
              _ = (t * z) * z⁻¹ := by rw [h1, hqz]
              _ = t := by group
          exact hs.Q_t q hq hqW ht_eq
    have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := by
      intro a ha b hb
      refine fzl_comm_mem_of_sq (N := Z) (hQsq a ha) (hQsq b hb)
        (hQsq (a * b) (mul_mem ha hb)) ?_
      intro n hn
      have h' : b * n * b⁻¹ = n := hs.Q_Z b hb n hn
      have hbn : b⁻¹ * n * b = n := by
        calc b⁻¹ * n * b = b⁻¹ * (b * n * b⁻¹) * b := by rw [h']
          _ = n := by group
      rw [hbn]
      exact hn
    exact hs.t_notin_E (hs.ZE (fzl_phi_le_of_elem hQcomm hQsq htΦ))
  · have hEΦ : E ≤ fzlPhi Q := by
      rw [← hYE_eq]
      exact inf_le_left
    refine le_antisymm hΦW ?_
    intro w hw
    rcases hs.W_split w hw with hwE | htwE
    · exact hEΦ hwE
    · have hw_eq : w = t * (t * w) := by rw [← mul_assoc, ← pow_two, hs.t_sq, one_mul]
      rw [hw_eq]
      exact mul_mem htΦ (hEΦ htwE)

end CFSG.OddStandard.SmallF3.FritzII
