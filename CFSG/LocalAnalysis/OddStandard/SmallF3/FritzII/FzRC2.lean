module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRS3C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzr_nc_lam
    (h : Ctx t L S x₁ x₂ lam rho tau) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P)
    (hlP : ∀ p ∈ P, lam * p * lam⁻¹ ∈ P) (hr3 : rho ^ 3 = 1) (hl2 : lam * lam = 1)
    (hl1 : lam ≠ 1) (hlr : lam * rho * lam⁻¹ = rho⁻¹)
    (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1) {p : G} (hp : p ∈ P) :
    ¬ ∃ g : G, g⁻¹ * t * g = p * lam := by
  rintro ⟨g, hg⟩
  have hordt : orderOf t = 2 := h.hyp.ord_t
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hordt]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordt
    norm_num at hordt
  have hu2 : (p * lam) * (p * lam) = 1 := by
    rw [← hg]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g)
        = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hu1 : p * lam ≠ 1 := by
    intro h1
    have hgt : g⁻¹ * t * g = 1 := by rw [hg, h1]
    have : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [hgt]; group
    exact ht1 this
  have huord : orderOf (p * lam) = 2 := by
    refine orderOf_eq_prime ?_ hu1
    rwa [pow_two]
  have hl2ord : orderOf lam = 2 := by
    refine orderOf_eq_prime ?_ hl1
    rwa [pow_two]
  obtain ⟨w, hwP, hw⟩ := fzr_conj_of_invol_mul hP2 hrP hlP hr3 hl2ord hlr hfpf hp huord
  have hlL : lam ∈ L := by
    have hl : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at hl
    exact hl.2
  obtain ⟨c, hcL, hc⟩ := h.invol_L lam hlL hl2 hl1
  have hm : g⁻¹ * t * g = (w * c) * (x₁ * x₂) ^ 2 * (w * c)⁻¹ := by
    calc g⁻¹ * t * g = p * lam := hg
      _ = w * lam * w⁻¹ := hw.symm
      _ = w * (c * (x₁ * x₂) ^ 2 * c⁻¹) * w⁻¹ := by rw [← hc]
      _ = (w * c) * (x₁ * x₂) ^ 2 * (w * c)⁻¹ := by group
  have hconj : ((w * c)⁻¹ * g⁻¹) * t * ((w * c)⁻¹ * g⁻¹)⁻¹ = (x₁ * x₂) ^ 2 := by
    have h1 : t = (g * (w * c)) * (x₁ * x₂) ^ 2 * (g * (w * c))⁻¹ := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = g * ((w * c) * (x₁ * x₂) ^ 2 * (w * c)⁻¹) * g⁻¹ := by rw [hm]
        _ = (g * (w * c)) * (x₁ * x₂) ^ 2 * (g * (w * c))⁻¹ := by group
    calc ((w * c)⁻¹ * g⁻¹) * t * ((w * c)⁻¹ * g⁻¹)⁻¹
        = (g * (w * c))⁻¹ * t * (g * (w * c)) := by group
      _ = (x₁ * x₂) ^ 2 := by rw [h1]; group
  exact S4A.not_conj_z_of_ctx h ⟨(w * c)⁻¹ * g⁻¹, hconj⟩

end CFSG.OddStandard.SmallF3.FritzII
