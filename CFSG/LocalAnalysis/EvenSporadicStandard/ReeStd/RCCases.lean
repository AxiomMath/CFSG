module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.RC

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem RC_cases (hS : 2 ∣ S.index) :
    H.RC S = H.DC S ⊔ S ∨ Nat.card (H.RC S) = 8 * Nat.card (H.DC S ⊔ S : Subgroup G) := by
  have hYR : H.DC S ⊔ S ≤ H.RC S := sup_le LocalSetting.DC_le_RC h.S_le_RC
  have hRN : H.RC S ≤ normalizer (S : Set G) := inf_le_right
  have hCnorm : H.CZ S ≤ normalizer ((H.RC S : Subgroup G) : Set G) := fun c hc =>
    h.N_le_normalizer_RC hc.2
  have hCR : H.RC S ⊓ H.CZ S = H.DC S := le_antisymm
    (fun x hx => LocalSetting.mem_DC_of_mem_CZ_of_mem_RC hx.2 hx.1)
    (le_inf LocalSetting.DC_le_RC LocalSetting.DC_le_CZ)
  have hDpos : 0 < Nat.card (H.DC S) := Nat.card_pos
  have hrel : (H.RC S).relIndex (H.CZ S) = 21 := by
    have h1 := Subgroup.relIndex_mul_card (H := H.RC S) (K := H.CZ S)
    rw [hCR, h.card_CZ] at h1
    exact Nat.eq_of_mul_eq_mul_right hDpos h1
  have hsup : 21 * Nat.card (H.RC S) = Nat.card ↥(H.CZ S ⊔ H.RC S) := by
    have h1 := Subgroup.relIndex_mul_card (H := H.RC S) (K := H.CZ S ⊔ H.RC S)
    rw [inf_eq_left.2 le_sup_right, relIndex_sup_right_of_le_normalizer hCnorm, hrel] at h1
    exact h1
  have hCRN : H.CZ S ⊔ H.RC S ≤ normalizer (S : Set G) := sup_le inf_le_right hRN
  have hdvd : 21 * Nat.card (H.RC S) ∣ 21 * (Nat.card Λ * Nat.card (H.DC S)) := by
    rw [hsup, ← mul_assoc, ← h.card_N hS]
    exact Subgroup.card_dvd_of_le hCRN
  have hdvd' : Nat.card (H.RC S) ∣ Nat.card Λ * Nat.card (H.DC S) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hΛD : Nat.card Λ * Nat.card (H.DC S) = 8 * Nat.card (H.DC S ⊔ S : Subgroup G) := by
    rw [h.card_sup_DC, h.card_DC, h.card_S]
    ring
  rw [hΛD] at hdvd'
  obtain ⟨m, hm⟩ : Nat.card (H.DC S ⊔ S : Subgroup G) ∣ Nat.card (H.RC S) :=
    Subgroup.card_dvd_of_le hYR
  have hYpos : 0 < Nat.card (H.DC S ⊔ S : Subgroup G) := Nat.card_pos
  have hm8 : m ∣ 8 := by
    rw [hm, mul_comm 8] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left hYpos hdvd'
  have hrelY : (H.DC S ⊔ S).relIndex (H.RC S) = m := by
    have h1 := Subgroup.relIndex_mul_card (H := H.DC S ⊔ S) (K := H.RC S)
    rw [inf_eq_left.2 hYR, hm] at h1
    exact Nat.eq_of_mul_eq_mul_right hYpos (h1.trans (mul_comm _ _))
  by_cases hm6 : m ≤ 6
  · left
    obtain ⟨σ, hσ, hσN⟩ := h.exists_sigma
    obtain ⟨a, ha⟩ := hσ.exists_pow_eq_one
    have hσC : σ ∈ H.CZ S := ⟨mem_centralizer_singleton_iff.2 hσ.comm_z, hσN⟩
    have hσR : σ ∈ normalizer ((H.RC S : Subgroup G) : Set G) := h.N_le_normalizer_RC hσN
    have hσY : σ ∈ normalizer ((H.DC S ⊔ S : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup (H.DC S) S ⟨h.CZ_le_normalizer_DC hσC, hσN⟩
    refine le_antisymm (fun r hr => ?_) hYR
    exact h.mem_SD_of_sigma_coset hσ hσN hr
      (conj_coset_fixed_pow (hrelY.le.trans hm6) ha hσR hσY hr)
  · right
    have h8 : m = 8 := by
      have := Nat.le_of_dvd (by norm_num) hm8
      rcases (by omega : m = 7 ∨ m = 8) with rfl | rfl
      · exact absurd hm8 (by norm_num)
      · rfl
    rw [hm, h8, mul_comm]

include h in
theorem exists_sylow_RC (hR : Nat.card (H.RC S) = 8 * Nat.card (H.DC S ⊔ S : Subgroup G)) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ S ≤ T ∧ T ≤ H.RC S ∧ Nat.card T = 8 * Nat.card S ∧
      Odd (T.relIndex (H.RC S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTp, hST, hTR, hTodd⟩ :=
    exists_isPGroup_le_odd_relIndex (A := H.RC S) h.pgroup h.S_le_RC
  refine ⟨T, hTp, hST, hTR, ?_, hTodd⟩
  obtain ⟨a, ha⟩ := hTp.exists_card_eq
  obtain ⟨b, hb⟩ := h.pgroup.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card (H := T) (K := H.RC S)
  rw [inf_eq_left.2 hTR] at h1
  rw [h.card_sup_DC] at hR
  refine eq_of_odd_mul_eq ⟨a, ha⟩ ⟨b + 3, ?_⟩ hTodd h.odd_relIndex_V_DC ?_
  · rw [pow_add, ← hb]
    ring
  · calc Nat.card T * T.relIndex (H.RC S) = T.relIndex (H.RC S) * Nat.card T := mul_comm _ _
      _ = Nat.card (H.RC S) := h1
      _ = 8 * (Nat.card S * H.V.relIndex (H.DC S)) := hR
      _ = 8 * Nat.card S * H.V.relIndex (H.DC S) := by ring

include h in
theorem RC_eq_of_forall_le (hS : 2 ∣ S.index)
    (hcase : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H.RC S → P ≤ S) : H.RC S = H.DC S ⊔ S := by
  rcases h.RC_cases hS with hR | hR
  · exact hR
  · exfalso
    obtain ⟨T, hTp, -, hTR, hTc, -⟩ := h.exists_sylow_RC hR
    have h1 : Nat.card T ≤ Nat.card S := Subgroup.card_le_of_le (hcase T hTp hTR)
    have hpos : 0 < Nat.card S := Nat.card_pos
    omega

end Stage

end CFSG.EvenSporadicStandard.ReeStd
