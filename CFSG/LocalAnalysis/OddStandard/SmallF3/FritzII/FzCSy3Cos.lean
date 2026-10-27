module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem fzc_eq_or_eq_or_eq_or_eq_of_card_four {V : Type*} [Finite V]
    (hV : Nat.card V = 4) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (w : V) :
    w = a ∨ w = b ∨ w = c ∨ w = d := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hsub : ({a, b, c, d} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  have hcard : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have huniv : (Finset.univ : Finset V).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hV]
  have heq : ({a, b, c, d} : Finset V) = Finset.univ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [huniv, hcard])
  have hw : w ∈ ({a, b, c, d} : Finset V) := by rw [heq]; exact Finset.mem_univ w
  simpa using hw

private theorem fzc_cos_rho_sq_eq_inv {rho : G} (hrho : rho ^ 3 = 1) : rho ^ 2 = rho⁻¹ := by
  have h : rho ^ 2 * rho = 1 := by rw [← pow_succ, hrho]
  exact mul_eq_one_iff_eq_inv.mp h

private theorem fzc_cos_conj_inv_eq {rho w : G} (hrho : rho ^ 3 = 1) :
    rho * (rho * w * rho⁻¹) * rho⁻¹ = rho⁻¹ * w * rho := by
  have h2 := fzc_cos_rho_sq_eq_inv hrho
  calc rho * (rho * w * rho⁻¹) * rho⁻¹
      = rho ^ 2 * w * (rho ^ 2)⁻¹ := by rw [pow_two]; group
    _ = rho⁻¹ * w * (rho⁻¹)⁻¹ := by rw [h2]
    _ = rho⁻¹ * w * rho := by group

private theorem fzc_quot_eq_iff {W Q : Subgroup G} {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    ((⟨a, ha⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) = ((⟨b, hb⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) ↔
      a⁻¹ * b ∈ W := by
  rw [QuotientGroup.eq]
  simp [Subgroup.mem_subgroupOf]

private theorem fzc_mul_inv_mem_of_quot_eq {W Q : Subgroup G}
    (hnrm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) {q b : G} (hq : q ∈ Q) (h : q⁻¹ * b ∈ W) :
    q * b⁻¹ ∈ W := by
  have h1 : b * q⁻¹ ∈ W := by
    have := hnrm q hq (q⁻¹ * b) h
    rwa [show q * (q⁻¹ * b) * q⁻¹ = b * q⁻¹ by group] at this
  have := W.inv_mem h1
  rwa [show (b * q⁻¹)⁻¹ = q * b⁻¹ by group] at this

theorem fzc_sy3_rho_cosets [Finite G] {W Q : Subgroup G} {rho : G} (hWQ : W ≤ Q)
    (hcard : Nat.card Q = 4 * Nat.card W) (hnrm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ W) (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ W)
    (hrQ : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q) (hrW : ∀ w ∈ W, rho * w * rho⁻¹ ∈ W)
    (hrho : rho ^ 3 = 1) (hfpf : ∀ q ∈ Q, rho * q * rho⁻¹ * q⁻¹ ∈ W → q ∈ W)
    {x : G} (hx : x ∈ Q) (hxW : x ∉ W) :
    ∀ q ∈ Q, q ∈ W ∨ q * x⁻¹ ∈ W ∨ q * (rho * x * rho⁻¹)⁻¹ ∈ W ∨
      q * (rho⁻¹ * x * rho)⁻¹ ∈ W := by
  haveI hWnorm : (W.subgroupOf Q).Normal := ⟨fun n hn g => by
    simp only [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnrm (g : G) g.2 (n : G) hn⟩
  have hrWinv : ∀ w ∈ W, rho⁻¹ * w * rho ∈ W := by
    intro w hw
    rw [← fzc_cos_conj_inv_eq hrho]
    exact hrW _ (hrW w hw)
  have hx₂ : rho * x * rho⁻¹ ∈ Q := hrQ x hx
  have hx₃ : rho⁻¹ * x * rho ∈ Q := by
    rw [show rho⁻¹ * x * rho = rho * (rho * x * rho⁻¹) * rho⁻¹ from
      (fzc_cos_conj_inv_eq hrho).symm]
    exact hrQ _ hx₂
  have hDcard : Nat.card (↥Q ⧸ W.subgroupOf Q) = 4 := by
    have hW'card : Nat.card (W.subgroupOf Q) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf Q)
    haveI : Nonempty ↥W := ⟨⟨1, W.one_mem⟩⟩
    haveI : Finite ↥W := inferInstance
    have hWpos : 0 < Nat.card W := Nat.card_pos
    have h : Nat.card (↥Q ⧸ W.subgroupOf Q) * Nat.card (W.subgroupOf Q) =
        4 * Nat.card (W.subgroupOf Q) := by
      rw [← hlag, hcard, hW'card]
    rw [hW'card] at h
    exact Nat.eq_of_mul_eq_mul_right hWpos h
  have h1x : (1 : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨x, hx⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have : (1 : G)⁻¹ * x ∈ W := (fzc_quot_eq_iff Q.one_mem hx).mp h
    simpa using this
  have h1x₂ : (1 : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨rho * x * rho⁻¹, hx₂⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have h2 : rho * x * rho⁻¹ ∈ W := by
      simpa using (fzc_quot_eq_iff Q.one_mem hx₂).mp h
    have := hrWinv _ h2
    rwa [show rho⁻¹ * (rho * x * rho⁻¹) * rho = x by group] at this
  have h1x₃ : (1 : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨rho⁻¹ * x * rho, hx₃⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have h3 : rho⁻¹ * x * rho ∈ W := by
      simpa using (fzc_quot_eq_iff Q.one_mem hx₃).mp h
    have := hrW _ h3
    rwa [show rho * (rho⁻¹ * x * rho) * rho⁻¹ = x by group] at this
  have hxx₂ : ((⟨x, hx⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨rho * x * rho⁻¹, hx₂⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have h' : x⁻¹ * (rho * x * rho⁻¹) ∈ W := (fzc_quot_eq_iff hx hx₂).mp h
    have hc : rho * x * rho⁻¹ * x⁻¹ ∈ W := by
      have := hnrm x hx (x⁻¹ * (rho * x * rho⁻¹)) h'
      rwa [show x * (x⁻¹ * (rho * x * rho⁻¹)) * x⁻¹ = rho * x * rho⁻¹ * x⁻¹ by group] at this
    exact hfpf x hx hc
  have hxx₃ : ((⟨x, hx⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨rho⁻¹ * x * rho, hx₃⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have h' : x⁻¹ * (rho⁻¹ * x * rho) ∈ W := (fzc_quot_eq_iff hx hx₃).mp h
    have hx₃x : (rho⁻¹ * x * rho) * x⁻¹ ∈ W := by
      have := hnrm x hx (x⁻¹ * (rho⁻¹ * x * rho)) h'
      rwa [show x * (x⁻¹ * (rho⁻¹ * x * rho)) * x⁻¹ =
        (rho⁻¹ * x * rho) * x⁻¹ by group] at this
    have hconj : rho * ((rho⁻¹ * x * rho) * x⁻¹) * rho⁻¹ ∈ W := hrW _ hx₃x
    have hfin : rho * x * rho⁻¹ * x⁻¹ ∈ W := by
      have := W.inv_mem hconj
      rwa [show (rho * ((rho⁻¹ * x * rho) * x⁻¹) * rho⁻¹)⁻¹ =
        rho * x * rho⁻¹ * x⁻¹ by group] at this
    exact hfpf x hx hfin
  have hx₂x₃ : ((⟨rho * x * rho⁻¹, hx₂⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) ≠
      ((⟨rho⁻¹ * x * rho, hx₃⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q) := by
    intro h
    apply hxW
    have h' : (rho * x * rho⁻¹)⁻¹ * (rho⁻¹ * x * rho) ∈ W := (fzc_quot_eq_iff hx₂ hx₃).mp h
    have hx₂x₃mem : (rho * x * rho⁻¹) * (rho⁻¹ * x * rho)⁻¹ ∈ W := by
      have h1 : (rho⁻¹ * x * rho) * (rho * x * rho⁻¹)⁻¹ ∈ W := by
        have := hnrm (rho * x * rho⁻¹) hx₂
          ((rho * x * rho⁻¹)⁻¹ * (rho⁻¹ * x * rho)) h'
        rwa [show (rho * x * rho⁻¹) * ((rho * x * rho⁻¹)⁻¹ * (rho⁻¹ * x * rho)) *
          (rho * x * rho⁻¹)⁻¹ = (rho⁻¹ * x * rho) * (rho * x * rho⁻¹)⁻¹ by group] at this
      have := W.inv_mem h1
      rwa [show ((rho⁻¹ * x * rho) * (rho * x * rho⁻¹)⁻¹)⁻¹ =
        (rho * x * rho⁻¹) * (rho⁻¹ * x * rho)⁻¹ by group] at this
    have hb : rho⁻¹ * x * rho = rho * (rho * x * rho⁻¹) * rho⁻¹ :=
      (fzc_cos_conj_inv_eq hrho).symm
    have hconj : rho⁻¹ * ((rho * x * rho⁻¹) * (rho⁻¹ * x * rho)⁻¹) * rho ∈ W :=
      hrWinv _ hx₂x₃mem
    have hfin : rho * x * rho⁻¹ * x⁻¹ ∈ W := by
      have := W.inv_mem hconj
      rwa [show (rho⁻¹ * ((rho * x * rho⁻¹) * (rho⁻¹ * x * rho)⁻¹) * rho)⁻¹ =
        rho * x * rho⁻¹ * x⁻¹ by rw [hb]; group] at this
    exact hfpf x hx hfin
  intro q hq
  have hcases := fzc_eq_or_eq_or_eq_or_eq_of_card_four hDcard
    (a := (1 : ↥Q ⧸ W.subgroupOf Q)) (b := ((⟨x, hx⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q))
    (c := ((⟨rho * x * rho⁻¹, hx₂⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q))
    (d := ((⟨rho⁻¹ * x * rho, hx₃⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q))
    h1x h1x₂ h1x₃ hxx₂ hxx₃ hx₂x₃ ((⟨q, hq⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q)
  rcases hcases with h | h | h | h
  · left
    have hm : q⁻¹ * (1 : G) ∈ W := (fzc_quot_eq_iff hq Q.one_mem).mp h
    simpa using W.inv_mem hm
  · right; left
    exact fzc_mul_inv_mem_of_quot_eq hnrm hq ((fzc_quot_eq_iff hq hx).mp h)
  · right; right; left
    exact fzc_mul_inv_mem_of_quot_eq hnrm hq ((fzc_quot_eq_iff hq hx₂).mp h)
  · right; right; right
    exact fzc_mul_inv_mem_of_quot_eq hnrm hq ((fzc_quot_eq_iff hq hx₃).mp h)


end CFSG.OddStandard.SmallF3.FritzII
