module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Frattini
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Complement
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.CaseI
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.RCCases

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem next (hR : Nat.card (H.RC S) = 8 * Nat.card (H.DC S ⊔ S : Subgroup G)) :
    ∃ T Λ' : Subgroup G, Nat.card T = 8 * Nat.card S ∧ Stage H T Λ' ∧ 2 ∣ T.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := H.simple
  obtain ⟨R, hR2, hSR, hRR, hRcard, hRodd⟩ := h.exists_sylow_RC hR
  have hRN : R ≤ normalizer (S : Set G) := hRR.trans inf_le_right
  have hRcard16 : Nat.card R = 16 * Nat.card Λ := by
    have := h.card_S
    omega
  have hΛR : Λ ≤ R := h.le.trans hSR
  have hΛn : ∀ r ∈ R, ∀ l ∈ Λ, r * l * r⁻¹ ∈ Λ := fun r hr l hl => h.N_normalizes_Λ (hRN hr) hl
  have hEcentral : ∀ r ∈ R, ∀ e ∈ H.E, r * e = e * r := fun r hr e he =>
    (Subgroup.mem_centralizer_iff.1 (hRR hr).1 e he).symm
  have hccentral : ∀ r ∈ R, H.z * r * H.z⁻¹ * r⁻¹ ∈ Λ := by
    intro r hr
    obtain ⟨hw, hwΛ⟩ := h.N_conj_mem (hRN hr) h.z_mem h.z_not_mem
    have h1 := h.mul_inv_mem_Λ hw hwΛ h.z_mem h.z_not_mem
    have h2 := h.z_normalizes h1
    have e : H.z * ((r * H.z * r⁻¹)⁻¹ * H.z) * H.z⁻¹ = H.z * r * H.z⁻¹ * r⁻¹ := by group
    rwa [e] at h2
  obtain ⟨σ, hσ, hσS, hσR⟩ := h.exists_sigma_next hR2 hSR hRR hRcard hRodd
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.N_le_normalizer_Λ hσS
  have hσc : σ * H.z * σ⁻¹ = H.z := by
    rw [hσ.comm_z]
    group
  have hσ7 : ∀ r ∈ R, σ ^ 7 * r * (σ ^ 7)⁻¹ = r :=
    h.pow_seven_apply_of_mem hR2 hRN hσ hσS hσR
  have hfree : ∀ r ∈ R, (σ * r * σ⁻¹ * r⁻¹ ∈ Λ ∨ σ * r * σ⁻¹ * r⁻¹ * H.z ∈ Λ) →
      (r ∈ Λ ∨ r * H.z ∈ Λ) := by
    intro r hr hprem
    have hmem : σ * r * σ⁻¹ * r⁻¹ ∈ S := by
      rcases hprem with h1 | h1
      · exact h.le h1
      · have e : σ * r * σ⁻¹ * r⁻¹ = (σ * r * σ⁻¹ * r⁻¹ * H.z) * H.z⁻¹ := by group
        rw [e]
        exact mul_mem (h.le h1) (inv_mem h.z_mem)
    have hrY : r ∈ H.DC S ⊔ S :=
      h.mem_SD_of_sigma_coset hσ hσS (hRR hr) (Subgroup.mem_sup_right hmem)
    have hrS : r ∈ S :=
      h.le_S_of_isPGroup_of_le_sup_DC (hR2.to_le (zpowers_le.2 hr)) (zpowers_le.2 hrY)
        (mem_zpowers r)
    exact h.cover r hrS
  obtain ⟨hcomm, hsq, W, hWR, hΛW, hzW, hWcard, hWσ, hWcover, hWtrans⟩ :=
    exists_complement' hΛR hΛn hRcard16 (hSR h.z_mem) h.z_not_mem H.z_mul_self hccentral
      hσR hσΛ hσ7 hσc hfree
  have hW2 : W.relIndex R = 2 := by
    have := Subgroup.relIndex_mul_card (H := W) (K := R)
    rw [inf_eq_left.2 hWR] at this
    have hpos : 0 < Nat.card W := Nat.card_pos
    nlinarith
  rcases h.dichotomy hR2 hSR hRcard hcomm hEcentral hσ hσS hσR hWR hΛW hWcard hWcover
    hWtrans with hXS | hzX
  · exfalso
    have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({H.z} : Set G) →
        centralizer ({H.z} : Set G) ⊓ R ≤ P → P ≤ R := by
      intro P hP hPC hRP
      have hVR : H.V ≤ R := h.V_le.trans hSR
      have hVP : H.V ≤ P := (le_inf H.V_le_centralizer hVR).trans hRP
      have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact (H.star hP hPC).1)
      rw [← this]
      exact hVR
    have hinv : ∀ n ∈ normalizer (R : Set G), ∃ s ∈ R, n * H.z * n⁻¹ = s * H.z * s⁻¹ := by
      intro n hn
      have hnz : n * H.z * n⁻¹ ∈ R := (mem_normalizer_iff.1 hn H.z).1 (hSR h.z_mem)
      have hnc : IsConj H.z (n * H.z * n⁻¹) := _root_.isConj_iff.2 ⟨n, rfl⟩
      have hnS : n * H.z * n⁻¹ ∈ S := hXS _ hnz hnc
      have hnΛ : n * H.z * n⁻¹ ∉ Λ := fun hh => h.not_isConj_of_mem hh hnc
      have hl : (n * H.z * n⁻¹) * H.z⁻¹ ∈ Λ := by
        rw [H.z_inv]
        exact (h.cover _ hnS).resolve_left hnΛ
      obtain ⟨r, hrR, hr⟩ := h.class_coset_exists hR2 hSR hRcard hcomm hEcentral (hSR h.z_mem)
        (IsConj.refl H.z) hl
      refine ⟨r, hrR, ?_⟩
      calc n * H.z * n⁻¹ = (n * H.z * n⁻¹ * H.z⁻¹) * H.z := by group
        _ = r * H.z * r⁻¹ := hr
    have hnotdvd := J1Std.not_two_dvd_index_of_invariant hR2 hmax hinv
    have hdvd := J1Std.two_dvd_index_of_avoid H.nonabelian hR2 hWR hW2 (hSR h.z_mem) hzW
      H.order_z
      (fun g hg => by
        have hgR : g⁻¹ * H.z * g ∈ R := hWR hg
        have hgc : IsConj H.z (g⁻¹ * H.z * g) := _root_.isConj_iff.2 ⟨g⁻¹, by simp⟩
        have hgS := hXS _ hgR hgc
        have hgΛ : g⁻¹ * H.z * g ∉ Λ := fun hh => h.not_isConj_of_mem hh hgc
        have h1 := (h.cover _ hgS).resolve_left hgΛ
        exact hzW (by
          have h2 := mul_mem (inv_mem hg) (hΛW h1)
          have e : (g⁻¹ * H.z * g)⁻¹ * (g⁻¹ * H.z * g * H.z) = H.z := by group
          rwa [e] at h2))
    exact hnotdvd hdvd
  ·
    have hzinv : ∀ a ∈ W, H.z * a * H.z = a⁻¹ := by
      intro a ha
      have h1 := H.sq_of_isConj (hzX a ha)
      calc H.z * a * H.z = (H.z * a * (H.z * a)) * a⁻¹ := by group
        _ = a⁻¹ := by rw [h1]; group
    have hstage : Stage H R W := by
      refine ⟨hR2, hWR, hSR h.z_mem, hzW, hWcover, h.E_le.trans hΛW, fun s hs hsW => ?_,
        h.noconj_E, fun b hb => ?_⟩
      · have h1 : s * H.z ∈ W := (hWcover s hs).resolve_left hsW
        have h3 : H.z * s = (s * H.z)⁻¹ := by
          have := hzinv _ h1
          calc H.z * s = H.z * s * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
            _ = H.z * (s * H.z) * H.z := by group
            _ = (s * H.z)⁻¹ := this
        have h4 : s = H.z * (H.z * s) := by
          calc s = (H.z * H.z) * s := by rw [H.z_mul_self, one_mul]
            _ = H.z * (H.z * s) := by group
        rw [h4]
        exact hzX _ (h3 ▸ inv_mem h1)
      · obtain ⟨c, hc, -, hcact⟩ := h.cov_next hR2 hSR hRR hRcard hRodd b hb
        exact ⟨c, hc, hcact⟩
    refine ⟨R, W, hRcard, hstage, ?_⟩
    exact J1Std.two_dvd_index_of_avoid H.nonabelian hR2 hWR hW2 (hSR h.z_mem) hzW H.order_z
      (fun g hg => hstage.not_isConj_of_mem hg (_root_.isConj_iff.2 ⟨g⁻¹, by simp⟩))

end Stage

end CFSG.EvenSporadicStandard.ReeStd
