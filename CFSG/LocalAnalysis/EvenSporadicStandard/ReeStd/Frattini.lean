module

import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.RC

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem exists_conj_z_of_card {T : Subgroup G} (hT2 : IsPGroup 2 T) (hST : S ≤ T)
    (hTN : T ≤ normalizer (S : Set G)) (hTcard : Nat.card T = 8 * Nat.card S) {w : G}
    (hwS : w ∈ S) (hwΛ : w ∉ Λ) : ∃ t ∈ T, w = t * H.z * t⁻¹ := by
  set C : Subgroup G := centralizer ({H.z} : Set G) ⊓ T with hC
  have hCp : IsPGroup 2 C := hT2.to_inf_right
  have hCle : Nat.card C ≤ 16 := (H.star hCp inf_le_left).1
  have hVT : H.V ≤ T := h.V_le.trans hST
  have hCge : 16 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le (le_inf H.V_le_centralizer hVT : H.V ≤ C)
    rwa [H.card_V] at this
  have hC16 : Nat.card C = 16 := le_antisymm hCle hCge
  have hTcard16 : Nat.card T = 16 * Nat.card Λ := by
    have := h.card_S
    omega
  have hcls := J1Std.card_eq_card_conjClass_mul T H.z
  rw [hC16, hTcard16] at hcls
  set A : Set G := {w | ∃ r ∈ T, w = r * H.z * r⁻¹} with hA
  set B : Set G := (fun l : G => l * H.z) '' (Λ : Set G) with hB
  have hAcard : A.ncard = Nat.card Λ := by
    have h1 : Nat.card {x : G // ∃ m ∈ T, x = m * H.z * m⁻¹} = A.ncard := by
      rw [← Nat.card_coe_set_eq]; rfl
    omega
  have hBcard : B.ncard = Nat.card Λ := by
    rw [hB, Set.ncard_image_of_injective _ (mul_left_injective H.z)]
    rw [← Nat.card_coe_set_eq]; rfl
  have hmemB : ∀ m ∈ S, m ∉ Λ → m ∈ B := by
    intro m hmS hmΛ
    refine ⟨m * H.z, (h.cover _ hmS).resolve_left hmΛ, ?_⟩
    show m * H.z * H.z = m
    rw [mul_assoc, H.z_mul_self, mul_one]
  have hAB : A ⊆ B := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hmS, hmΛ⟩ := h.N_conj_z_mem (hTN hr)
    exact hmemB _ hmS hmΛ
  have hAeq : A = B := Set.eq_of_subset_of_ncard_le hAB (by omega) (Set.toFinite B)
  have hwB := hmemB w hwS hwΛ
  rw [← hAeq] at hwB
  exact hwB

include h in
theorem cov_next {T : Subgroup G} (hT2 : IsPGroup 2 T) (hST : S ≤ T) (hTR : T ≤ H.RC S)
    (hTcard : Nat.card T = 8 * Nat.card S) (hodd : Odd (T.relIndex (H.RC S))) :
    ∀ b ∈ H.B, ∃ c ∈ centralizer ({H.z} : Set G) ⊓ normalizer (T : Set G),
      c ∈ normalizer (S : Set G) ∧ ∀ e ∈ H.E, c * e * c⁻¹ = b * e * b⁻¹ := by
  intro b hb
  have hTN : T ≤ normalizer (S : Set G) := hTR.trans inf_le_right
  have hcent : ∀ g ∈ H.RC S, ∀ x ∈ H.E, g * x * g⁻¹ = x := fun g hg x hx => by
    have := Subgroup.mem_centralizer_iff.1 hg.1 x hx
    rw [← this]
    group
  obtain ⟨c, hc, hcb⟩ := h.cov b hb
  have hcR : c ∈ normalizer ((H.RC S : Subgroup G) : Set G) := h.N_le_normalizer_RC hc.2
  obtain ⟨r, hr, hrc⟩ := exists_mul_mem_normalizer_of_sylow hTR hT2 hodd hcR
  have hn : r * c ∈ normalizer (S : Set G) := mul_mem hr.2 hc.2
  obtain ⟨hnS, hnΛ⟩ := h.N_conj_z_mem hn
  obtain ⟨t, ht, htn⟩ := h.exists_conj_z_of_card hT2 hST hTN hTcard hnS hnΛ
  have hcz : (t⁻¹ * (r * c)) * H.z * (t⁻¹ * (r * c))⁻¹ = H.z := by
    calc (t⁻¹ * (r * c)) * H.z * (t⁻¹ * (r * c))⁻¹
        = t⁻¹ * ((r * c) * H.z * (r * c)⁻¹) * t := by group
      _ = t⁻¹ * (t * H.z * t⁻¹) * t := by rw [htn]
      _ = H.z := by group
  refine ⟨t⁻¹ * (r * c), ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩, ?_, fun e he => ?_⟩
  · calc (t⁻¹ * (r * c)) * H.z = ((t⁻¹ * (r * c)) * H.z * (t⁻¹ * (r * c))⁻¹) * (t⁻¹ * (r * c)) := by
          group
      _ = H.z * (t⁻¹ * (r * c)) := by rw [hcz]
  · have htT : t ∈ normalizer (T : Set G) := le_normalizer ht
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htT) hrc
  · have htS : t ∈ normalizer (S : Set G) := hTN ht
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htS) hn
  · have hx : c * e * c⁻¹ ∈ H.E := h.N_conj_E hc.2 he
    have h1 := hcent r hr _ hx
    have h2 := hcent t⁻¹ (inv_mem (hTR ht)) _ hx
    rw [inv_inv] at h2
    calc (t⁻¹ * (r * c)) * e * (t⁻¹ * (r * c))⁻¹
        = t⁻¹ * (r * (c * e * c⁻¹) * r⁻¹) * t := by group
      _ = t⁻¹ * (c * e * c⁻¹) * t := by rw [h1]
      _ = c * e * c⁻¹ := h2
      _ = b * e * b⁻¹ := hcb e he

include h in
theorem centralizes_T_of_odd_pow {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ normalizer (S : Set G)) {g : G} (hgT : g ∈ normalizer (T : Set G)) {m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) (hgS : ∀ s ∈ S, g * s * g⁻¹ = s) :
    ∀ t ∈ T, g * t * g⁻¹ = t := by
  have hgS' : ∀ s ∈ S, g⁻¹ * s * g = s := by
    intro s hs
    calc g⁻¹ * s * g = g⁻¹ * (g * s * g⁻¹) * g := by rw [hgS s hs]
      _ = s := by group
  intro t ht
  have hgt : g * t * g⁻¹ ∈ T := (mem_normalizer_iff.1 hgT t).1 ht
  have huT : g * t * g⁻¹ * t⁻¹ ∈ T := mul_mem hgt (inv_mem ht)
  have huC : g * t * g⁻¹ * t⁻¹ ∈ centralizer (H.V : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have hvS : v ∈ S := h.V_le hv
    have hwS : t⁻¹ * v * t ∈ S := by
      have := (mem_normalizer_iff.1 (inv_mem (hTN ht)) v).1 hvS
      simpa using this
    have key : (g * t * g⁻¹ * t⁻¹) * v * (g * t * g⁻¹ * t⁻¹)⁻¹ = v := by
      calc (g * t * g⁻¹ * t⁻¹) * v * (g * t * g⁻¹ * t⁻¹)⁻¹
          = g * t * (g⁻¹ * (t⁻¹ * v * t) * g) * t⁻¹ * g⁻¹ := by group
        _ = g * t * (t⁻¹ * v * t) * t⁻¹ * g⁻¹ := by rw [hgS' _ hwS]
        _ = g * v * g⁻¹ := by group
        _ = v := hgS v hvS
    calc v * (g * t * g⁻¹ * t⁻¹) = ((g * t * g⁻¹ * t⁻¹) * v * (g * t * g⁻¹ * t⁻¹)⁻¹) *
          (g * t * g⁻¹ * t⁻¹) := by rw [key]
      _ = (g * t * g⁻¹ * t⁻¹) * v := by group
  have hu : g * t * g⁻¹ * t⁻¹ ∈ H.V :=
    H.le_V_of_isPGroup_of_le_centralizer_V (hT2.to_le (zpowers_le.2 huT)) (zpowers_le.2 huC)
      (mem_zpowers _)
  have hu1 := hgS _ (h.V_le hu)
  have hu2 := H.V_sq hu
  have hsq : g * (g * t * g⁻¹) * g⁻¹ = t := by
    calc g * (g * t * g⁻¹) * g⁻¹
        = (g * (g * t * g⁻¹ * t⁻¹) * g⁻¹) * (g * t * g⁻¹) := by group
      _ = (g * t * g⁻¹ * t⁻¹) * (g * t * g⁻¹) := by rw [hu1]
      _ = ((g * t * g⁻¹ * t⁻¹) * (g * t * g⁻¹ * t⁻¹)) * t := by group
      _ = t := by rw [hu2, one_mul]
  have hc2 : Commute (g ^ 2) t := by
    rw [pow_two]
    show g * g * t = t * (g * g)
    calc g * g * t = (g * (g * t * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = t * (g * g) := by rw [hsq]
  obtain ⟨k, hk⟩ := hm
  have hg : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, hgm, one_mul]
  have hcomm : Commute ((g ^ 2) ^ (k + 1)) t := hc2.pow_left (k + 1)
  rw [← hg] at hcomm
  rw [hcomm.eq]
  group

include h in
theorem pow_seven_apply_of_mem {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ normalizer (S : Set G)) {σ : G} (hσ : H.IsSigma σ)
    (hσS : σ ∈ normalizer (S : Set G)) (hσT : σ ∈ normalizer (T : Set G)) :
    ∀ t ∈ T, σ ^ 7 * t * (σ ^ 7)⁻¹ = t := by
  obtain ⟨a, ha⟩ := hσ.exists_pow_eq_one
  have h7odd : Odd (7 ^ a) := Odd.pow (by decide)
  have hg7 : (σ ^ 7) ^ 7 ^ a = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have hgS : ∀ s ∈ S, σ ^ 7 * s * (σ ^ 7)⁻¹ = s :=
    h.centralizes_S_of_odd_pow (pow_mem hσS 7) h7odd hg7 (fun e he => hσ.pow_seven_apply_E he)
      (hσ.pow_comm_z 7)
  exact h.centralizes_T_of_odd_pow hT2 hTN (pow_mem hσT 7) h7odd hg7 hgS

include h in
theorem exists_sigma_next {T : Subgroup G} (hT2 : IsPGroup 2 T) (hST : S ≤ T) (hTR : T ≤ H.RC S)
    (hTcard : Nat.card T = 8 * Nat.card S) (hodd : Odd (T.relIndex (H.RC S))) :
    ∃ σ : G, H.IsSigma σ ∧ σ ∈ normalizer (S : Set G) ∧ σ ∈ normalizer (T : Set G) := by
  obtain ⟨b, hb7⟩ := H.exists_order7_actB
  obtain ⟨c, hc, hcS, hcact⟩ := h.cov_next hT2 hST hTR hTcard hodd b b.2
  obtain ⟨k, hk⟩ := H.exists_isSigma_of_action (mem_centralizer_singleton_iff.1 hc.1) hb7 hcact
  exact ⟨c ^ k, hk, pow_mem hcS k, pow_mem hc.2 k⟩

end Stage

end CFSG.EvenSporadicStandard.ReeStd
