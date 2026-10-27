module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Fuse
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2019

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.GH74.KGroups
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}
  {M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8} {d : H₁.Data}

theorem psiC_congr {u v : H} (huv : u = v) (hu : u ∈ centralizer ({h.a * d.sigma} : Set H))
    (hv : v ∈ centralizer ({h.a * d.sigma} : Set H)) : psiC M d u hu = psiC M d v hv := by
  subst huv
  rfl

theorem psiC_one : psiC M d 1 (one_mem _) = 1 := by
  have he : (⟨h.x * d.g * 1 * (h.x * d.g)⁻¹, conj_c_mem_normalizer d (one_mem _)⟩ :
      normalizer (h.K : Set H)) = 1 := Subtype.ext (by
    change h.x * d.g * 1 * (h.x * d.g)⁻¹ = 1
    group)
  change psi M _ = 1
  rw [he, map_one]

theorem orderOf_psiC_dvd {u : H} (hu : u ∈ centralizer ({h.a * d.sigma} : Set H)) :
    orderOf (psiC M d u hu) ∣ orderOf u := by
  have h1 := orderOf_map_dvd (psi M)
    ⟨h.x * d.g * u * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hu⟩
  have h2 : orderOf (⟨h.x * d.g * u * (h.x * d.g)⁻¹, conj_c_mem_normalizer d hu⟩ :
      normalizer (h.K : Set H)) = orderOf u := by
    rw [Subgroup.orderOf_mk, show h.x * d.g * u * (h.x * d.g)⁻¹ =
      (h.x * d.g)⁻¹⁻¹ * u * (h.x * d.g)⁻¹ by rw [inv_inv], Hyp59.L81Hyp.Data.orderOf_conj_inv]
  rw [h2] at h1
  exact h1

theorem fused_of_dihedral (I : In81)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8)))
    (F : d.Facts) (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma) {e₁ e₂ θ : H}
    (he₁D : e₁ ∈ h.D) (he₂D : e₂ ∈ h.D) (he₁₁ : e₁ * e₁ = 1) (he₂₂ : e₂ * e₂ = 1)
    (he₁₂ : e₁ * e₂ = e₂ * e₁) (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1) (hne : e₁ ≠ e₂)
    (hθC : θ * (h.a * d.sigma) = h.a * d.sigma * θ) (hθP : ∀ π ∈ h.P, θ * π = π * θ)
    (hθo : Odd (orderOf θ)) (hθ₁ : θ * e₁ * θ⁻¹ = e₂) (hθ₂ : θ * e₂ * θ⁻¹ = e₁ * e₂)
    {q : H} (hqP : q ∈ h.P) (hq2 : q * q = h.a) (hbq : d.b * q * d.b⁻¹ = q⁻¹) :
    (∃ w : H, w⁻¹ * h.a * w = q * d.b) ∨ (∃ w : H, w⁻¹ * d.sigma * w = q * d.b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hP, hA, hΦ⟩ := exists_model H₁ I.cf1 I.cf2 hA8
  have hθ : θ ∈ centralizer ({h.a * d.sigma} : Set H) := mem_centralizer_singleton_iff.mpr hθC
  have hq := mem_C_of_mem_P I F h3 hqP
  have hpa : psiC M d h.a a_mem_C = psi M ⟨d.tau, le_normalizer d.tau_K⟩ := psiC_a I F
  have hps8 : psiC M d d.b b_mem_C = s8 := psiC_b hΦ
  have hpp : psiC M d q hq * psiC M d q hq = psi M ⟨d.tau, le_normalizer d.tau_K⟩ := by
    rw [← psiC_mul hq hq, psiC_congr hq2 _ a_mem_C, hpa]
  have hs8 : s8 * s8 = 1 := by decide
  have hsp : s8 * psiC M d q hq * s8 = (psiC M d q hq)⁻¹ := by
    have h1 : psiC M d (d.b * q * d.b⁻¹) (mul_mem (mul_mem b_mem_C hq) (inv_mem b_mem_C)) =
        psiC M d q⁻¹ (inv_mem hq) := psiC_congr hbq _ _
    rw [psiC_mul (mul_mem b_mem_C hq) (inv_mem b_mem_C), psiC_mul b_mem_C hq,
      psiC_inv b_mem_C, psiC_inv hq, hps8] at h1
    rwa [show s8⁻¹ = s8 from inv_eq_of_mul_eq_one_right hs8] at h1
  have hθq : psiC M d θ hθ * psiC M d q hq = psiC M d q hq * psiC M d θ hθ := by
    rw [← psiC_mul hθ hq, ← psiC_mul hq hθ]
    exact psiC_congr (hθP q hqP) _ _
  have hθs : psiC M d θ hθ * s8 = s8 * psiC M d θ hθ := by
    rw [← hps8, ← psiC_mul hθ b_mem_C, ← psiC_mul b_mem_C hθ]
    exact psiC_congr (hθP d.b d.b_mem_P) _ _
  have hθo' : psiC M d θ hθ ^ 315 = 1 :=
    pow_eq_one_of_odd (Odd.of_dvd_nat hθo (orderOf_psiC_dvd hθ))
  have hθ1 : psiC M d θ hθ ≠ 1 := by
    intro h1
    have he₁C := mem_C_of_mem_D F he₁D
    have he₂C := mem_C_of_mem_D F he₂D
    have hc1 : psiC M d e₂ he₂C = psiC M d e₁ he₁C := by
      rw [← psiC_congr hθ₁ (mul_mem (mul_mem hθ he₁C) (inv_mem hθ)) he₂C,
        psiC_mul (mul_mem hθ he₁C) (inv_mem hθ), psiC_mul hθ he₁C, psiC_inv hθ, h1, one_mul,
        inv_one, mul_one]
    have hc2 : psiC M d e₁ he₁C * psiC M d e₂ he₂C = psiC M d e₂ he₂C := by
      rw [← psiC_mul he₁C he₂C, ← psiC_congr hθ₂ (mul_mem (mul_mem hθ he₂C) (inv_mem hθ))
        (mul_mem he₁C he₂C), psiC_mul (mul_mem hθ he₂C) (inv_mem hθ), psiC_mul hθ he₂C,
        psiC_inv hθ, h1, one_mul, inv_one, mul_one]
    have hpe₁ : psiC M d e₁ he₁C = 1 := mul_right_cancel (hc2.trans (one_mul _).symm)
    have hpe₂ : psiC M d e₂ he₂C = 1 := hc1.trans hpe₁
    obtain ⟨hX4, -⟩ := card_sup_zpowers_of_inv he₁₁ he₂₂ he₁1 he₂1 hne he₁₂
    have hX2 : IsPGroup 2 ↥(zpowers e₁ ⊔ zpowers e₂) :=
      IsPGroup.of_card (n := 2) (by rw [hX4]; norm_num)
    have hXC : zpowers e₁ ⊔ zpowers e₂ ≤ centralizer ({h.a * d.sigma} : Set H) :=
      sup_le (zpowers_le.mpr he₁C) (zpowers_le.mpr he₂C)
    have hcomm : ∀ x ∈ zpowers e₁, ∀ y ∈ zpowers e₂, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow he₁₂ i j).eq
    have hle := card_le_two_of_psiC (M := M) hX2 hXC fun u hu => by
      obtain ⟨x, hx, y, hy, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hcomm hu
      have hxC : x ∈ centralizer ({h.a * d.sigma} : Set H) := hXC (mem_sup_left hx)
      have hyC : y ∈ centralizer ({h.a * d.sigma} : Set H) := hXC (mem_sup_right hy)
      change psiC M d (x * y) (mul_mem hxC hyC) = 1
      rw [psiC_mul hxC hyC]
      rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self he₁₁ hx with rfl | rfl <;>
        rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self he₂₂ hy with rfl | rfl
      · rw [psiC_one, one_mul]
      · rw [psiC_one, one_mul, hpe₂]
      · rw [psiC_one, mul_one, hpe₁]
      · rw [hpe₁, hpe₂, one_mul]
    omega
  obtain ⟨π, hπ, hπt⟩ := exists_conj_of_odd (psi_tau_mem I.cf1 I.cf2 F hP hA hΦ) hpp hsp hθ1
    hθo' hθq hθs
  have hqb2 : q * d.b * (q * d.b) = 1 := by
    have hb1 : d.b⁻¹ = d.b := inv_eq_of_mul_eq_one_right d.b_mul_self
    rw [hb1] at hbq
    rw [show q * d.b * (q * d.b) = q * (d.b * q * d.b) by group, hbq, mul_inv_cancel]
  exact fused_of_psiC I F hP hA (mul_mem hq b_mem_C) hqb2 hπ
    (by rw [psiC_mul hq b_mem_C, hps8, ← hπt])

end CFSG.ComponentClassification.GSThmB.A8
