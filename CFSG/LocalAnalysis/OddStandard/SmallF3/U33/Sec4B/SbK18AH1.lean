module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private lemma k18A_exists_fixed_coset {Q : Subgroup G} {ρ ν : G} (hρ3 : ρ ^ 3 = 1)
    (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hν : ρ * ν * ρ⁻¹ * ν⁻¹ ∈ Q) : ∃ x : G, x * ν⁻¹ ∈ Q ∧ ρ * x * ρ⁻¹ = x := by
  have hc : (ν⁻¹)⁻¹ * ρ * ν⁻¹ * ρ⁻¹ ∈ Q := by
    have e : (ν⁻¹)⁻¹ * ρ * ν⁻¹ * ρ⁻¹ = (ρ * ν * ρ⁻¹ * ν⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hν
  obtain ⟨q, hq, hfix⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.exists_fixed_coset Q ρ ν⁻¹ hρ3 hρQ hc hQ3
  refine ⟨q⁻¹ * ν, ?_, ?_⟩
  · have e : q⁻¹ * ν * ν⁻¹ = q⁻¹ := by group
    rw [e]
    exact inv_mem hq
  · have h1 : ρ * (ν⁻¹ * q) * ρ⁻¹ = ν⁻¹ * q := by rw [hfix]; group
    calc ρ * (q⁻¹ * ν) * ρ⁻¹ = (ρ * (ν⁻¹ * q) * ρ⁻¹)⁻¹ := by group
      _ = (ν⁻¹ * q)⁻¹ := by rw [h1]
      _ = q⁻¹ * ν := by group

private lemma k18A_rho_sq {ρ : G} (hρ3 : ρ ^ 3 = 1) : ρ * ρ = ρ⁻¹ ∧ ρ⁻¹ * ρ⁻¹ = ρ := by
  have h : ρ * ρ * ρ = 1 := by simpa [pow_succ] using hρ3
  have h1 : ρ * ρ = ρ⁻¹ := eq_inv_of_mul_eq_one_left h
  refine ⟨h1, ?_⟩
  calc ρ⁻¹ * ρ⁻¹ = ρ⁻¹ * (ρ * ρ) := by rw [h1]
    _ = ρ := by group

private lemma k18A_conj_inv_of_sq {ξ w : G} (hw2 : w * w = 1) (h : (ξ * w) * (ξ * w) = 1) :
    w * ξ * w⁻¹ = ξ⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right hw2]
  have h' : ξ * (w * ξ * w) = 1 := by
    calc ξ * (w * ξ * w) = (ξ * w) * (ξ * w) := by group
      _ = 1 := h
  exact eq_inv_of_mul_eq_one_right h'

private lemma k18A_conj_inv_rho {ρ w : G} (hwρ : w * ρ * w⁻¹ = ρ⁻¹) : w * ρ⁻¹ * w⁻¹ = ρ := by
  have h : w * ρ⁻¹ * w⁻¹ = (w * ρ * w⁻¹)⁻¹ := by group
  rw [h, hwρ, inv_inv]

private lemma k18A_conj_conj {ρ ξ w : G} (hwρ : w * ρ * w⁻¹ = ρ⁻¹) (hwξ : w * ξ * w⁻¹ = ξ⁻¹) :
    w * (ρ * ξ * ρ⁻¹) * w⁻¹ = (ρ⁻¹ * ξ * ρ)⁻¹ := by
  have hwρ' := k18A_conj_inv_rho hwρ
  calc w * (ρ * ξ * ρ⁻¹) * w⁻¹ = (w * ρ * w⁻¹) * (w * ξ * w⁻¹) * (w * ρ⁻¹ * w⁻¹) := by group
    _ = ρ⁻¹ * ξ⁻¹ * ρ := by rw [hwρ, hwξ, hwρ']
    _ = (ρ⁻¹ * ξ * ρ)⁻¹ := by group

private lemma k18A_conj_norm {ρ a : G} (hρ3 : ρ ^ 3 = 1) :
    ρ * (a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ)) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) * a := by
  obtain ⟨hρρ, hρinv2⟩ := k18A_rho_sq hρ3
  have hbc : ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * a * ρ := by
    calc ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * a * (ρ⁻¹ * ρ⁻¹) := by group
      _ = ρ⁻¹ * a * ρ := by rw [hρρ, hρinv2]
  calc ρ * (a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ)) * ρ⁻¹
      = (ρ * a * ρ⁻¹) * (ρ * (ρ * a * ρ⁻¹) * ρ⁻¹) * (ρ * (ρ⁻¹ * a * ρ) * ρ⁻¹) := by group
    _ = (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) * a := by rw [hbc]; group

private lemma k18A_norm_mem {Ξ Q : Subgroup G} {ρ ξ : G} (hρ3 : ρ ^ 3 = 1) (hQΞ : Q ≤ Ξ)
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hcomm : ∀ a ∈ Ξ, ∀ b ∈ Ξ, a * b * a⁻¹ * b⁻¹ ∈ Q)
    (hρΞ : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ ∈ Ξ) (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q)
    (hfix : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ = x → x = 1) (hξ : ξ ∈ Ξ) :
    ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ) ∈ Q := by
  obtain ⟨hρρ, hρinv2⟩ := k18A_rho_sq hρ3
  have hbΞ : ρ * ξ * ρ⁻¹ ∈ Ξ := hρΞ ξ hξ
  have hcΞ : ρ⁻¹ * ξ * ρ ∈ Ξ := by
    have h : ρ * (ρ * ξ * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * ξ * ρ := by
      calc ρ * (ρ * ξ * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * ξ * (ρ⁻¹ * ρ⁻¹) := by group
        _ = ρ⁻¹ * ξ * ρ := by rw [hρρ, hρinv2]
    rw [← h]
    exact hρΞ _ hbΞ
  have hνΞ : ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ) ∈ Ξ := mul_mem (mul_mem hξ hbΞ) hcΞ
  have hν : ρ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ)) * ρ⁻¹ *
      (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ ∈ Q := by
    have h := hcomm ξ⁻¹ (inv_mem hξ) _ hνΞ
    have e : ρ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ)) * ρ⁻¹ *
        (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ =
        ξ⁻¹ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ)) * (ξ⁻¹)⁻¹ *
        (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ := by
      rw [k18A_conj_norm hρ3]; group
    rw [e]; exact h
  obtain ⟨x, hxQ, hxfix⟩ := k18A_exists_fixed_coset hρ3 hρQ hQ3 hν
  have hxΞ : x ∈ Ξ := by
    have e : x = (x * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹) *
        (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ)) := by group
    rw [e]
    exact mul_mem (hQΞ hxQ) hνΞ
  have hx1 : x = 1 := hfix x hxΞ hxfix
  rw [hx1, one_mul] at hxQ
  exact inv_mem_iff.mp hxQ

theorem k18A_cocycle_exact {Ξ Q : Subgroup G} {ρ w : G} (hρ3 : ρ ^ 3 = 1) (hw2 : w * w = 1)
    (hwρ : w * ρ * w⁻¹ = ρ⁻¹) (hQΞ : Q ≤ Ξ) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hQn : ∀ x ∈ Ξ, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hcomm : ∀ a ∈ Ξ, ∀ b ∈ Ξ, a * b * a⁻¹ * b⁻¹ ∈ Q) (hsq : ∀ a ∈ Ξ, a * a ∈ Q)
    (hρΞ : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ ∈ Ξ) (hρQ : ∀ q ∈ Q, ρ * q * ρ⁻¹ ∈ Q)
    (hfix : ∀ x ∈ Ξ, ρ * x * ρ⁻¹ = x → x = 1) {ξ : G} (hξ : ξ ∈ Ξ)
    (hξw : (ξ * w) * (ξ * w) = 1) : ∃ η ∈ Ξ, ξ * w = η * w * η⁻¹ := by
  obtain ⟨hρρ, hρinv2⟩ := k18A_rho_sq hρ3
  have hwξ : w * ξ * w⁻¹ = ξ⁻¹ := k18A_conj_inv_of_sq hw2 hξw
  have hbΞ : ρ * ξ * ρ⁻¹ ∈ Ξ := hρΞ ξ hξ
  have hνQ := k18A_norm_mem hρ3 hQΞ hQ3 hcomm hρΞ hρQ hfix hξ
  have hξ₁Q : (ρ * ξ * ρ⁻¹)⁻¹ * ξ * (ρ⁻¹ * ξ * ρ)⁻¹ ∈ Q := by
    have hq1 : ξ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ * ξ⁻¹ ∈ Q :=
      hQn ξ hξ _ (inv_mem hνQ)
    have hq : (ξ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ * ξ⁻¹) * (ξ * ξ) ∈ Q :=
      mul_mem hq1 (hsq ξ hξ)
    have h := hQn (ρ * ξ * ρ⁻¹)⁻¹ (inv_mem hbΞ) _ hq
    have e : (ρ * ξ * ρ⁻¹)⁻¹ * ξ * (ρ⁻¹ * ξ * ρ)⁻¹ =
        (ρ * ξ * ρ⁻¹)⁻¹ * ((ξ * (ξ * (ρ * ξ * ρ⁻¹) * (ρ⁻¹ * ξ * ρ))⁻¹ * ξ⁻¹) * (ξ * ξ)) *
        ((ρ * ξ * ρ⁻¹)⁻¹)⁻¹ := by group
    rw [e]; exact h
  have hξ₁w : ((ρ * ξ * ρ⁻¹)⁻¹ * ξ * (ρ⁻¹ * ξ * ρ)⁻¹) * w =
      (ρ * ξ * ρ⁻¹)⁻¹ * (ξ * w) * (ρ * ξ * ρ⁻¹) := by
    have hwb := k18A_conj_conj hwρ hwξ
    calc ((ρ * ξ * ρ⁻¹)⁻¹ * ξ * (ρ⁻¹ * ξ * ρ)⁻¹) * w
        = (ρ * ξ * ρ⁻¹)⁻¹ * ξ * (w * (ρ * ξ * ρ⁻¹) * w⁻¹) * w := by rw [hwb]
      _ = (ρ * ξ * ρ⁻¹)⁻¹ * (ξ * w) * (ρ * ξ * ρ⁻¹) := by group
  generalize hbdef : ρ * ξ * ρ⁻¹ = b at hbΞ hξ₁Q hξ₁w
  generalize hadef : b⁻¹ * ξ * (ρ⁻¹ * ξ * ρ)⁻¹ = a at hξ₁Q hξ₁w
  have hcoc : (a * w) * (a * w) = 1 := by
    rw [hξ₁w]
    calc b⁻¹ * (ξ * w) * b * (b⁻¹ * (ξ * w) * b) = b⁻¹ * ((ξ * w) * (ξ * w)) * b := by group
      _ = 1 := by rw [hξw]; group
  have hwa : w * a * w⁻¹ = a⁻¹ := k18A_conj_inv_of_sq hw2 hcoc
  have hb₂Q : ρ * a * ρ⁻¹ ∈ Q := hρQ a hξ₁Q
  have hc₂Q : ρ⁻¹ * a * ρ ∈ Q := by
    have h : ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * a * ρ := by
      calc ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * a * (ρ⁻¹ * ρ⁻¹) := by group
        _ = ρ⁻¹ * a * ρ := by rw [hρρ, hρinv2]
    rw [← h]
    exact hρQ _ hb₂Q
  have hn₂Q : a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) ∈ Q := mul_mem (mul_mem hξ₁Q hb₂Q) hc₂Q
  have hn₂fix : ρ * (a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ)) * ρ⁻¹ =
      a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) := by
    rw [k18A_conj_norm hρ3]
    have h := hQab ((ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ)) (mul_mem hb₂Q hc₂Q) a hξ₁Q
    calc ρ * a * ρ⁻¹ * (ρ⁻¹ * a * ρ) * a = (ρ * a * ρ⁻¹ * (ρ⁻¹ * a * ρ)) * a := rfl
      _ = a * (ρ * a * ρ⁻¹ * (ρ⁻¹ * a * ρ)) := h
      _ = a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) := by group
  have hn₂one : a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ) = 1 :=
    hfix _ (hQΞ hn₂Q) hn₂fix
  have hwη₂ : w * (a * (ρ * a * ρ⁻¹)) * w⁻¹ = a⁻¹ * (ρ⁻¹ * a * ρ)⁻¹ := by
    have h := k18A_conj_conj hwρ hwa
    calc w * (a * (ρ * a * ρ⁻¹)) * w⁻¹ = (w * a * w⁻¹) * (w * (ρ * a * ρ⁻¹) * w⁻¹) := by group
      _ = a⁻¹ * (ρ⁻¹ * a * ρ)⁻¹ := by rw [hwa, h]
  have hη₂ : a * w = (a * (ρ * a * ρ⁻¹)) * w * (a * (ρ * a * ρ⁻¹))⁻¹ := by
    calc a * w = (a * (ρ * a * ρ⁻¹) * (ρ⁻¹ * a * ρ)) * a * w := by rw [hn₂one]; group
      _ = (a * (ρ * a * ρ⁻¹)) * (a⁻¹ * (ρ⁻¹ * a * ρ)⁻¹)⁻¹ * w := by group
      _ = (a * (ρ * a * ρ⁻¹)) * (w * (a * (ρ * a * ρ⁻¹)) * w⁻¹)⁻¹ * w := by rw [hwη₂]
      _ = (a * (ρ * a * ρ⁻¹)) * w * (a * (ρ * a * ρ⁻¹))⁻¹ := by group
  refine ⟨b * (a * (ρ * a * ρ⁻¹)), mul_mem hbΞ (hQΞ (mul_mem hξ₁Q hb₂Q)), ?_⟩
  calc ξ * w = b * (b⁻¹ * (ξ * w) * b) * b⁻¹ := by group
    _ = b * (a * w) * b⁻¹ := by rw [← hξ₁w]
    _ = b * ((a * (ρ * a * ρ⁻¹)) * w * (a * (ρ * a * ρ⁻¹))⁻¹) * b⁻¹ := by rw [← hη₂]
    _ = (b * (a * (ρ * a * ρ⁻¹))) * w * (b * (a * (ρ * a * ρ⁻¹)))⁻¹ := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
