module

public import CFSG.FeitThompson.Representations.ExteriorImageProportionalCentralCoefficients
public import CFSG.FeitThompson.Representations.ConstantCharacterCentralSectionCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

namespace IsTINormalCentralSection

variable {p : ℕ} {P : Sylow p G} {L Z : Subgroup G} {h : ℕ}

theorem exists_int_dvd_sub_of_mem_signedIrr [Finite G]
    (hs : IsTINormalCentralSection p P L Z h) {ψ : G → ℂ} (hψ : ψ ∈ signedIrr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → ψ z = c) :
    ∃ a b : ℤ, c = a ∧ ψ 1 = b ∧ (Nat.card (P : Subgroup G) : ℤ) ∣ b - a := by
  rcases mem_signedIrr.1 hψ with hIrr | hIrr
  · exact hs.exists_int_dvd_sub hIrr hc
  · obtain ⟨a, b, ha, hb, hdvd⟩ := hs.exists_int_dvd_sub_neg hIrr (c := c)
      (fun z hz hz1 => by simpa using hc z hz hz1)
    exact ⟨a, b, ha, by simpa using hb, hdvd⟩

end IsTINormalCentralSection

namespace IsFreeCentralSection

variable {p a : ℕ} {L P E Z : Subgroup G} (h : IsFreeCentralSection p a L P E Z)

include h

theorem isTINormalCentralSection [Finite G] :
    IsTINormalCentralSection p h.sylow L Z (Nat.card P) where
  prime := h.prime
  sylow_ne_bot := by rw [h.coe_sylow]; exact h.P_ne_bot
  normalizer_eq := by rw [h.coe_sylow]; exact h.normalizer_eq
  odd_natCard := h.odd_natCard_L
  ti := by simpa only [h.coe_sylow] using h.inter_conj_eq_empty
  Z_ne_bot := h.Z_ne_bot
  Z_le_center := by rw [h.coe_sylow]; exact h.Z_le_center
  le_normalizer_Z := h.le_normalizer_Z
  natCard_centralizer_inf_eq := fun _ hz hz1 => by rw [h.inf_centralizer_eq_P hz hz1]

variable [Fintype G] [Fintype ↥L] [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem exists_int_resClassFun_eq_add_zsmul
    (ν : Submodule.span ℤ (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hν : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {ψ : G → ℂ} (hψ : ψ ∈ signedIrr G)
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0) :
    ∃ lam : ℤ, ∃ Ξ ∈ Submodule.span ℤ (irrTrivialOn (Z.subgroupOf L)),
      resClassFun L ψ = Ξ + (lam : ℂ) • centralLayerWeightedChar (P.subgroupOf L)
            ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) ∧
        ∀ z : ↥L, (z : G) ∈ Z → z ≠ 1 →
          ψ (1 : G) - ψ (z : G) = (lam : ℂ) * (Nat.card P : ℂ) := by
  obtain ⟨lam, Ξ, hΞ, hdec, hval⟩ :=
    h.exists_resClassFun_eq_add_smul_centralLayerWeightedChar ν hν hψ horth
  set c : ℂ := ψ 1 - (lam : ℂ) * (Nat.card P : ℂ) with hcdef
  have hc : ∀ z ∈ Z, z ≠ 1 → ψ z = c := by
    intro z hz hz1
    have hz' := hval ⟨z, h.Z_le hz⟩ hz (by simpa using hz1)
    rw [hcdef]
    linear_combination -hz'
  obtain ⟨A₀, B₀, hA₀, hB₀, hdvd⟩ :=
    h.isTINormalCentralSection.exists_int_dvd_sub_of_mem_signedIrr hψ hc
  obtain ⟨k, hk⟩ := hdvd
  have hPne : ((Nat.card P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [show Nat.card ((h.sylow : Subgroup G)) = Nat.card P by rw [h.coe_sylow]] at hk
  have hkC : (B₀ : ℂ) - (A₀ : ℂ) = (Nat.card P : ℂ) * (k : ℂ) := by
    have hcast := congrArg (fun n : ℤ => (n : ℂ)) hk
    push_cast at hcast
    linear_combination hcast
  have hlamC : (lam : ℂ) = (k : ℂ) := by
    have h1 : (B₀ : ℂ) - (A₀ : ℂ) = (lam : ℂ) * (Nat.card P : ℂ) := by
      rw [← hB₀, ← hA₀, hcdef]; ring
    exact mul_right_cancel₀ hPne (by linear_combination h1.symm.trans hkC)
  exact ⟨k, Ξ, hΞ, by rw [hdec, hlamC], fun z hz hz1 => by rw [hval z hz hz1, hlamC]⟩

theorem exists_int_resClassFun_eq_add_zsmul_of_isCoherentWith
    (τ : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (ν : Submodule.span ℤ (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hcoh : IsCoherentWith (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) τ ν)
    {ψ : G → ℂ} (hψ : ψ ∈ signedIrr G)
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0) :
    ∃ lam : ℤ, ∃ Ξ ∈ Submodule.span ℤ (irrTrivialOn (Z.subgroupOf L)),
      resClassFun L ψ = Ξ + (lam : ℂ) • centralLayerWeightedChar (P.subgroupOf L)
            ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) ∧
        ∀ z : ↥L, (z : G) ∈ Z → z ≠ 1 →
          ψ (1 : G) - ψ (z : G) = (lam : ℂ) * (Nat.card P : ℂ) :=
  h.exists_int_resClassFun_eq_add_zsmul ν
    (fun f => by rw [hcoh.eq_on_zero f, hτ f]) hψ horth

end IsFreeCentralSection

end CFSG.FeitThompson
