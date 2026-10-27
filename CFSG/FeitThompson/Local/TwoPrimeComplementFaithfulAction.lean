module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {G : Type u} [Group G] [Finite G]

namespace IsReducedPrimeCentralizerKernel

variable {p q : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P)

include hc

theorem exists_mulEquiv_quotient_frattini :
    ∃ d, Nat.card (↥K ⧸ frattini ↥K) = q ^ d ∧
      Nonempty (↥K ⧸ frattini ↥K ≃* (Fin d → Multiplicative (ZMod q))) :=
  exists_mulEquiv_quotient_frattini_of_isPGroup hc.prime_q hc.isPGroup_K

theorem le_normalizer_inf_centralizer :
    P ⊔ R ≤ normalizer (((P ⊔ R) ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg,
      normalizer_le_normalizer_centralizer K (hc.sup_le_normalizer_K hg)⟩

theorem inf_P_centralizer_eq_bot : P ⊓ centralizer (K : Set G) = ⊥ := by
  have hPH : P ≤ H := hc.P_le_N.trans hc.isPrimeCentralizerKernelSetup.N_le_H
  have hle : P ⊓ centralizer (K : Set G) ≤ P ⊓ K :=
    le_inf inf_le_left ((inf_le_inf_right _ hPH).trans hc.inf_H_centralizer_K_le)
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥P) := by
    rw [hc.card_P]; exact hc.coprime_card_K.pow_right _
  have hd : Nat.Coprime (Nat.card ↥(P ⊓ K)) (Nat.card ↥(P ⊓ K)) :=
    (hcop.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right)).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hone : Nat.card ↥(P ⊓ K) = 1 := by simpa [Nat.Coprime] using hd
  exact le_bot_iff.1 (Subgroup.card_eq_one.1 hone ▸ hle)

theorem inf_R_centralizer_eq_bot : R ⊓ centralizer (K : Set G) = ⊥ := by
  have hr : (Nat.card ↥R0).Prime := hc.admissible.prime_card
  have hRR0 : Nat.card ↥R = Nat.card ↥R0 := by rw [hc.R_eq]
  have hdvd : Nat.card ↥(R ⊓ centralizer (K : Set G)) ∣ Nat.card ↥R0 :=
    hRR0 ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have hEq : R ⊓ centralizer (K : Set G) = R :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hRR0])
    have hRle : R ≤ centralizer (K : Set G) := hEq ▸ inf_le_right
    rw [hc.R_eq] at hRle
    exact hc.isPrimeCentralizerKernelSetup.not_le_centralizer_K hRle

theorem sup_inf_centralizer_eq_bot : (P ⊔ R) ⊓ centralizer (K : Set G) = ⊥ := by
  set C : Subgroup G := (P ⊔ R) ⊓ centralizer (K : Set G) with hCdef
  have hnorm := hc.le_normalizer_inf_centralizer
  have hCP : C ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← hc.inf_P_centralizer_eq_bot, hCdef]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hCR : C ⊓ R = ⊥ := by
    rw [eq_bot_iff, ← hc.inf_R_centralizer_eq_bot, hCdef]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hEdvd : Nat.card ↥(P ⊔ R) ∣ Nat.card ↥P * Nat.card ↥R :=
    ⟨Nat.card ↥(P ⊓ R),
      (natCard_sup_mul_natCard_inf_of_le_normalizer hc.R_le_normalizer_P).symm⟩
  have hCPcard : Nat.card ↥(C ⊔ P) = Nat.card ↥C * Nat.card ↥P := by
    have h := natCard_sup_mul_natCard_inf_of_le_normalizer (S := C) (T := P)
      (le_sup_left.trans hnorm)
    rw [hCP] at h; simpa using h
  have hCRcard : Nat.card ↥(C ⊔ R) = Nat.card ↥C * Nat.card ↥R := by
    have h := natCard_sup_mul_natCard_inf_of_le_normalizer (S := C) (T := R)
      (le_sup_right.trans hnorm)
    rw [hCR] at h; simpa using h
  have hdvdR : Nat.card ↥C ∣ Nat.card ↥R := by
    have h1 : Nat.card ↥C * Nat.card ↥P ∣ Nat.card ↥R * Nat.card ↥P := by
      rw [← hCPcard, mul_comm (Nat.card ↥R)]
      exact (Subgroup.card_dvd_of_le (sup_le inf_le_left le_sup_left)).trans hEdvd
    exact (Nat.mul_dvd_mul_iff_right Nat.card_pos).1 h1
  have hdvdP : Nat.card ↥C ∣ Nat.card ↥P := by
    have h1 : Nat.card ↥C * Nat.card ↥R ∣ Nat.card ↥P * Nat.card ↥R := by
      rw [← hCRcard]
      exact (Subgroup.card_dvd_of_le (sup_le inf_le_left le_sup_right)).trans hEdvd
    exact (Nat.mul_dvd_mul_iff_right Nat.card_pos).1 h1
  have hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥P) := by
    have hpr : p ≠ Nat.card ↥R0 :=
      have : Fact p.Prime := ⟨hc.prime_p⟩
      ne_natCard_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal
    rw [hc.card_P, hc.R_eq]
    exact ((Nat.coprime_primes hc.admissible.prime_card hc.prime_p).2 (Ne.symm hpr)).pow_right _
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hdvdR hdvdP))

theorem injective_action : Function.Injective hc.action := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : (g : G) ∈ (P ⊔ R) ⊓ centralizer (K : Set G) := by
    refine mem_inf.2 ⟨g.2, mem_centralizer_iff.2 fun x hx => ?_⟩
    have h2 := congrArg (fun f : MulAut ↥K => ((f (⟨x, hx⟩ : ↥K) : ↥K) : G)) hg
    simp only [hc.coe_action_apply] at h2
    have h3 : (g : G) * x * (g : G)⁻¹ = x := by simpa using h2
    calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * g := by rw [h3]
      _ = (g : G) * x := by group
  rw [hc.sup_inf_centralizer_eq_bot, mem_bot] at hmem
  exact Subtype.ext hmem

theorem ker_action_eq_bot : hc.action.ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff hc.action).2 hc.injective_action

theorem injective_frattiniQuotientAction :
    Function.Injective (frattiniQuotientAction hc.action) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hker : hc.action g ∈ autKerFrattini ↥K := frattiniQuotientAction_eq_one_iff.1 hg
  have hq : IsPGroup q ↥(autKerFrattini ↥K) :=
    isPGroup_autKerFrattini_of_isPGroup hc.prime_q hc.isPGroup_K
  have h1 : hc.action g = 1 :=
    hc.isMinimalInvariantAction.apply_eq_one_of_mem_isPGroup hq hker
  exact (injective_iff_map_eq_one _).1 hc.injective_action g h1

theorem ker_frattiniQuotientAction_eq_bot : (frattiniQuotientAction hc.action).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2 hc.injective_frattiniQuotientAction

theorem primeCentralizerFaithfulQuotientAction :
    (P ⊔ R) ⊓ centralizer (K : Set G) = ⊥ ∧
      Function.Injective (frattiniQuotientAction hc.action) :=
  ⟨hc.sup_inf_centralizer_eq_bot, hc.injective_frattiniQuotientAction⟩

end IsReducedPrimeCentralizerKernel

end CFSG.FeitThompson

end

