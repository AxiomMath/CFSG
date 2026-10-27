module

public import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise MulAction

universe u

variable {G : Type u} [Group G] {p q : ℕ}

def conjInvariantSubMulAction {A' : Subgroup (ConjAct G)} {S : Set (Subgroup G)}
    (h : ∀ a ∈ A', ∀ W ∈ S, a • W ∈ S) : SubMulAction ↥A' (Subgroup G) where
  carrier := S
  smul_mem' c _ hW := h c c.2 _ hW

@[simp] theorem mem_conjInvariantSubMulAction {A' : Subgroup (ConjAct G)} {S : Set (Subgroup G)}
    (h : ∀ a ∈ A', ∀ W ∈ S, a • W ∈ S) {W : Subgroup G} :
    W ∈ conjInvariantSubMulAction h ↔ W ∈ S := Iff.rfl

theorem natCard_conjInvariantSubMulAction {A' : Subgroup (ConjAct G)} {S : Set (Subgroup G)}
    (h : ∀ a ∈ A', ∀ W ∈ S, a • W ∈ S) :
    Nat.card ↥(conjInvariantSubMulAction h) = S.ncard := Nat.card_coe_set_eq S

namespace IsTransitiveHyperplaneSetup

variable [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsTransitiveHyperplaneSetup p q d H R R0 V K U N P)

include hc

theorem ncard_eq_natCard_R0 : (hyperplaneFixedSubgroups q V K).ncard = Nat.card ↥R0 := by
  rcases hc.ncard_eq_or with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := hc.reduced.admissible.odd_card_subgroup R0
    obtain ⟨m, hm⟩ := h ▸ hc.odd_ncard
    omega

theorem not_dvd_natCard_R0 : ¬ p ∣ Nat.card ↥R0 := by
  have hPH : P ≤ H := hc.reduced.P_le_N.trans (hc.reduced.N_eq ▸ inf_le_right)
  have hcardP := hc.reduced.card_P
  have ha : (Nat.card ↥N).factorization p ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcardP
    exact hc.reduced.P_ne_bot (Subgroup.card_eq_one.1 hcardP)
  have hpH : p ∣ Nat.card ↥H := (hcardP ▸ dvd_pow_self p ha).trans (Subgroup.card_dvd_of_le hPH)
  intro hd
  have hd' : p ∣ Nat.card ↥R := hc.natCard_R ▸ hd
  have h1 : p ∣ 1 := hc.reduced.admissible.coprime ▸ Nat.dvd_gcd hpH hd'
  exact hc.prime_p.one_lt.ne' (Nat.dvd_one.1 h1)

theorem exists_mem_fixed_of_P : ∃ W ∈ hyperplaneFixedSubgroups q V K,
    ∀ g ∈ P, ConjAct.toConjAct g • W = W := by
  have := Fact.mk hc.prime_p
  set A' : Subgroup (ConjAct G) := P.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom with hA'
  have hstable : ∀ a ∈ A', ∀ W ∈ hyperplaneFixedSubgroups q V K,
      a • W ∈ hyperplaneFixedSubgroups q V K := by
    rintro a ⟨g, hg, rfl⟩ W hW
    exact hc.smul_mem_hyperplaneFixedSubgroups (Subgroup.mem_sup_left hg) hW
  have hA'card : Nat.card ↥A' = p ^ (Nat.card ↥N).factorization p := by
    rw [hA', ← hc.reduced.card_P]
    exact (Nat.card_congr
      (P.equivMapOfInjective _ (ConjAct.toConjAct (G := G)).injective).toEquiv).symm
  obtain ⟨W, hWfix⟩ := nonempty_fixedPoints_of_not_dvd_natCard (P := ↥A')
    (X := ↥(conjInvariantSubMulAction hstable)) hA'card
    (by rw [natCard_conjInvariantSubMulAction, hc.ncard_eq_natCard_R0]; exact hc.not_dvd_natCard_R0)
  exact ⟨W, W.2, fun g hg =>
    congrArg Subtype.val (hWfix (⟨ConjAct.toConjAct g, ⟨g, hg, rfl⟩⟩ : ↥A'))⟩

end IsTransitiveHyperplaneSetup

theorem not_isTransitiveHyperplaneSetup [Finite G] {d : ℕ} {H R R0 V K U N P : Subgroup G} :
    ¬ IsTransitiveHyperplaneSetup p q d H R R0 V K U N P := by
  intro hc
  obtain ⟨W, hWmem, hWP⟩ := hc.exists_mem_fixed_of_P
  have : IsCyclic ↥W := hc.isCyclic_of_mem_hyperplaneFixedSubgroups hWmem
  have hKW : K ≤ normalizer (W : Set G) := hc.K_le_normalizer_of_mem hWmem
  have hPW : P ≤ normalizer (W : Set G) := fun g hg =>
    Subgroup.conjAct_pointwise_smul_iff.1 (hWP g hg)
  have hKcent : K ≤ centralizer (W : Set G) := by
    rw [hc.reduced.K_eq_commutator, Subgroup.commutator_le]
    intro k hk g hg
    exact commutatorElement_mem_centralizer_of_isCyclic (hKW hk) (hPW hg)
  refine ne_bot_of_mem_hyperplaneFixedSubgroups hWmem (le_bot_iff.1 ?_)
  rw [← hc.reduced.inf_V_centralizer_K]
  refine le_inf (le_of_mem_hyperplaneFixedSubgroups hWmem) fun x hx => ?_
  rw [mem_centralizer_iff]
  exact fun k hk => ((mem_centralizer_iff.1 (hKcent hk)) x hx).symm

end

end CFSG.FeitThompson
