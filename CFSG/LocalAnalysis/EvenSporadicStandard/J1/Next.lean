module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step2
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Complement
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.CaseI

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem next (hR : Nat.card (H.RC S) = 8 * Nat.card S) :
    ∃ Λ' : Subgroup G, Stage H (H.RC S) Λ' ∧ 2 ∣ (H.RC S).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := H.simple
  set R := H.RC S with hRdef
  have hSR : S ≤ R := h.S_le_RC
  have hRN : R ≤ normalizer (S : Set G) := inf_le_right
  have hR2 : IsPGroup 2 R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.pgroup
    exact IsPGroup.of_card (n := k + 3) (by rw [hR, hk]; ring)
  have hRcard16 : Nat.card R = 16 * Nat.card Λ := by
    have := h.card_S
    omega
  have hΛR : Λ ≤ R := h.le.trans hSR
  have hΛn : ∀ r ∈ R, ∀ l ∈ Λ, r * l * r⁻¹ ∈ Λ := fun r hr l hl => h.N_normalizes_Λ (hRN hr) hl
  have hEcentral : ∀ r ∈ R, ∀ e ∈ H.E, r * e = e * r := fun r hr e he =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).1 e he).symm
  have hccentral : ∀ r ∈ R, H.z * r * H.z⁻¹ * r⁻¹ ∈ Λ := by
    intro r hr
    obtain ⟨hw, hwΛ⟩ := h.N_conj_mem (hRN hr) h.z_mem h.z_not_mem
    have h1 := h.mul_inv_mem_Λ hw hwΛ h.z_mem h.z_not_mem
    have h2 := h.z_normalizes h1
    have e : H.z * ((r * H.z * r⁻¹)⁻¹ * H.z) * H.z⁻¹ = H.z * r * H.z⁻¹ * r⁻¹ := by group
    rwa [e] at h2
  obtain ⟨σ, hσNL, hσ7⟩ := H.exists_sigma
  have hσB : σ ∈ H.B := H.NL_le_B hσNL
  have hσR : σ ∈ normalizer (R : Set G) := h.N_le_normalizer_RC (h.B_S hσB)
  have hσL : σ ∈ H.L := (H.mem_NL_iff.1 hσNL).1
  have hσ7' : σ ^ 7 = 1 := by rw [← hσ7]; exact pow_orderOf_eq_one σ
  have hσc : σ * H.z * σ⁻¹ = H.z := by
    calc σ * H.z * σ⁻¹ = H.z * σ * σ⁻¹ := by rw [H.comm_z hσL]
      _ = H.z := by group
  have hfree : ∀ r ∈ R, (σ * r * σ⁻¹ * r⁻¹ ∈ Λ ∨ σ * r * σ⁻¹ * r⁻¹ * H.z ∈ Λ) →
      (r ∈ Λ ∨ r * H.z ∈ Λ) := by
    intro r hr hprem
    have hmem : σ * r * σ⁻¹ * r⁻¹ ∈ S := by
      rcases hprem with h1 | h1
      · exact h.le h1
      · have e : σ * r * σ⁻¹ * r⁻¹ = (σ * r * σ⁻¹ * r⁻¹ * H.z) * H.z⁻¹ := by group
        rw [e]
        exact mul_mem (h.le h1) (inv_mem h.z_mem)
    exact h.cover r (h.mem_S_of_sigma_coset hσNL hσ7 hr hmem)
  obtain ⟨hcomm, hsq, W, hWR, hΛW, hzW, hWcard, hWσ, hWcover, hWtrans⟩ :=
    exists_complement hΛR hΛn hRcard16 (hSR h.z_mem) h.z_not_mem H.z_mul_self hccentral
      hσR (h.B_Λ hσB) hσ7' hσc hfree
  have hW2 : W.relIndex R = 2 := by
    have := Subgroup.relIndex_mul_card (H := W) (K := R)
    rw [inf_eq_left.2 hWR] at this
    have hpos : 0 < Nat.card W := Nat.card_pos
    nlinarith
  rcases h.dichotomy hR2 hSR hR hcomm hEcentral hσB hσR hWR hΛW hWcard hWcover hWtrans with
    hXS | hzX
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
      obtain ⟨r, hrR, hr⟩ := h.class_coset_exists hR2 hSR hR hcomm hEcentral (hSR h.z_mem)
        (IsConj.refl H.z) hl
      refine ⟨r, hrR, ?_⟩
      calc n * H.z * n⁻¹ = (n * H.z * n⁻¹ * H.z⁻¹) * H.z := by group
        _ = r * H.z * r⁻¹ := hr
    have hnotdvd := not_two_dvd_index_of_invariant hR2 hmax hinv
    have hdvd := two_dvd_index_of_avoid H.nonabelian hR2 hWR hW2 (hSR h.z_mem) hzW H.order_z
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
        h.noconj_E, fun b hb => h.N_le_normalizer_RC (h.B_S hb)⟩
      have h1 : s * H.z ∈ W := (hWcover s hs).resolve_left hsW
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
    refine ⟨W, hstage, ?_⟩
    exact two_dvd_index_of_avoid H.nonabelian hR2 hWR hW2 (hSR h.z_mem) hzW H.order_z
      (fun g hg => hstage.not_isConj_of_mem hg (_root_.isConj_iff.2 ⟨g⁻¹, by simp⟩))

end Stage

end CFSG.EvenSporadicStandard.J1Std
