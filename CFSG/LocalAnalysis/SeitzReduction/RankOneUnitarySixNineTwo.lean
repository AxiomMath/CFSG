module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Char

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem exists_conj_t_of_sq_eq_one (hU : U3U1Data G L f t T R₂ U₁)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {u : G} (hu : u ∈ U₁) (hu2 : (u * t) ^ 2 = 1) :
    ∃ w ∈ U₁, w * t * w⁻¹ = u * t := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have htinv : t⁻¹ = t := hR.t_inv
  have htR : t ∈ normalizer (R₂ : Set G) := mem_normalizer_iff.mpr fun r =>
    ⟨fun hr => hR.tN r hr, fun hr => by
      have := hR.tN _ hr
      rwa [htinv, show t * (t * r * t) * t = (t * t) * r * (t * t) by group, htt, one_mul,
        mul_one] at this⟩
  refine conj_of_free_series htt htR (le_sup_right.trans hU.le)
    (fun r hr => by rw [← sq]; exact hU.sq_R₂ r hr) hU.comm_mem
    (fun x hx => by rw [← sq]; exact hU.sq_mem x hx) (fun r hr hrt => ?_) (fun x hx hxt => ?_)
    hu (by rw [← sq]; exact hu2)
  · have hrA : r ∈ szA₁ (szT₁ L T) := hR.rho_ker r hr (by
      calc r * t = (t * r * t⁻¹) * t := by rw [hrt]
        _ = t * r := by group)
    obtain ⟨s, hs, hst⟩ := hR.rho_onto r hrA
    exact ⟨s, hs, by rw [htinv]; exact hst⟩
  · have hxt' : x * t * x⁻¹ * t⁻¹ ∈ R₂ := by
      have := inv_mem hxt
      rwa [show (t * x * t⁻¹ * x⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ by group] at this
    exact hU.exists_inv_comm_mul_mem hR (hU.mem_sup_of_comm_mem hR htt hx hxt')

end U3U1Data

section Certificates

theorem u3SixNineInput_of_conj (hconj : U3SixNineConjInput) : U3SixNineInput :=
  u3SixNineInput_of_free_of_conj u3SixNineFreeInput_holds hconj

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem normalizer_sup_le_of_not_isCyclic (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) :
    normalizer ((U₁ ⊔ T : Subgroup G) : Set G) ≤
      normalizer (R₂ : Set G) ⊓ normalizer (U₁ : Set G) := by
  obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := u3SplitInput G L f t T h hS2 hncyc
  exact hU.normalizer_sup_le_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S

theorem exists_conj_of_sq_eq_one_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁) {x : G}
    (hx : x ∈ U₁ ⊔ T) (hx2 : x ^ 2 = 1) (hxU : x ∉ U₁) :
    ∃ w ∈ U₁, w * t * w⁻¹ = x ∨ w * v * w⁻¹ = x ∨ w * (t * v) * w⁻¹ = x := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hnC : ∀ w ∈ T, w ∉ szT₁ L T ⊔ zpowers t → w ∉ centralizer (R₂ : Set G) := by
    intro w hwT hwS hwC
    have hwU : w ∈ U₁ := hC (mem_inf.mpr ⟨mem_sup_right hwT, hwC⟩)
    have hwT₁ : w ∈ szT₁ L T := by rw [← hU.inf_eq h hR]; exact mem_inf.mpr ⟨hwU, hwT⟩
    exact hwS (mem_sup_left hwT₁)
  have htvT : t * v ∈ T := mul_mem htT hvT
  have htv2 : (t * v) ^ 2 = 1 := by
    have e : t * v * (t * v) = (t * t) * (v * v) := by
      calc t * v * (t * v) = t * (v * t) * v := by group
        _ = t * (t * v) * v := by rw [hvt]
        _ = (t * t) * (v * v) := by group
    rw [sq, e, ← sq, ← sq, h.sq_eq_one, hv2, one_mul]
  have htvS : t * v ∉ szT₁ L T ⊔ zpowers t := fun hm => hvS (by
    have := mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm
    rwa [inv_mul_cancel_left] at this)
  have hv2' : v ^ 2 ∈ szT₁ L T := by rw [hv2]; exact one_mem _
  obtain ⟨u, hu, h1 | h1 | h1 | h1⟩ := hU.exists_eq_of_sq_eq_one h hS2 hR hvT hv2' hvS hx hx2
  · exact absurd (h1 ▸ hu) hxU
  · obtain ⟨w, hw, hwt⟩ := hU.exists_conj_t_of_sq_eq_one hR hu (by rw [← h1]; exact hx2)
    exact ⟨w, hw, Or.inl (by rw [hwt, h1])⟩
  · obtain ⟨w, hw, hwv⟩ := u3SixNineFreeInput_holds G L f t T R₂ U₁ h hS2 hR hU v hvT hv2 hvS
      (hnC v hvT hvS) u hu (by rw [← h1]; exact hx2)
    exact ⟨w, hw, Or.inr (Or.inl (by rw [hwv, h1]))⟩
  · obtain ⟨w, hw, hwv⟩ := u3SixNineFreeInput_holds G L f t T R₂ U₁ h hS2 hR hU (t * v) htvT
      htv2 htvS (hnC _ htvT htvS) u hu (by rw [← mul_assoc, ← h1]; exact hx2)
    exact ⟨w, hw, Or.inr (Or.inr (by rw [hwv, h1, mul_assoc]))⟩

end U3U1Data

end Certificates

end CFSG.SeitzReduction.RankOne
