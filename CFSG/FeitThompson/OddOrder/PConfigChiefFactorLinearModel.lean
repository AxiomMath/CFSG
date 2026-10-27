module

public import CFSG.FeitThompson.OddOrder.ChiefFactorFaithfulLinearImage
public import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.OddOrder.ChiefFactorAboveCoprimeCentralizer

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup ChiefFactorFaithfulImage ChiefFactorFixedLine ChiefFactorLinearAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {M : Type*} [Group M]

theorem zpowers_eq_of_mem_of_ne_one {B : Subgroup M} (hB : (Nat.card ↥B).Prime) {b : M}
    (hb : b ∈ B) (hb1 : b ≠ 1) : zpowers b = B := by
  have := Fact.mk hB
  refine le_antisymm (zpowers_le.2 hb) fun x hx => ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card (p := Nat.card ↥B) rfl (g := ⟨b, hb⟩)
      (by simpa [Subtype.ext_iff] using hb1) (g' := ⟨x, hx⟩))
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg (Subgroup.subtype B) hn⟩

section Kernel

variable {H U H₀ : Subgroup M} [H.Normal] [H₀.Normal] (p : ℕ) {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

theorem actionKernel_eq_ker (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    actionKernel p H H₀ U e = ((factorLinearAut p H H₀ e).comp U.subtype).ker := by
  ext u
  rw [mem_actionKernel, MonoidHom.mem_ker]
  rfl

theorem range_comp_subtype_eq_factorLinearImage
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    ((factorLinearAut p H H₀ e).comp U.subtype).range = factorLinearImage p H H₀ U e := by
  ext f
  rw [MonoidHom.mem_range, mem_factorLinearImage]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, u.2, hu⟩, fun ⟨u, hu, h⟩ => ⟨⟨u, hu⟩, h⟩⟩

noncomputable def quotientActionKernelMulEquiv
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    (↥U ⧸ actionKernel p H H₀ U e) ≃* factorLinearImage p H H₀ U e :=
  (QuotientGroup.quotientMulEquivOfEq (actionKernel_eq_ker p e)).trans
    ((QuotientGroup.quotientKerEquivRange ((factorLinearAut p H H₀ e).comp U.subtype)).trans
      (MulEquiv.subgroupCongr (range_comp_subtype_eq_factorLinearImage p e)))

theorem coe_quotientActionKernelMulEquiv_mk
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (u : ↥U) :
    (quotientActionKernelMulEquiv p e (QuotientGroup.mk u) : V ≃ₗ[ZMod p] V)
      = factorLinearAut p H H₀ e (u : M) := (rfl)

end Kernel

variable {H J U B F W2 H₀ : Subgroup M} {q : ℕ}

theorem IsPTypeConfig.exists_isChiefFactor (hc : IsPTypeConfig H J U B F W2) :
    ∃ H₀ : Subgroup M, IsChiefFactor H H₀ ∧ H ⊓ centralizer (U : Set M) ≤ H₀ := by
  have := hc.finite
  have := hc.normal_H
  have := hc.isNilpotent_H
  obtain ⟨H₀, hH₀n, hH₀lt, hH₀le, hmax⟩ :=
    exists_normal_maximal_centralizer_le (A := U ⊔ B) hc.isComplement'_H_sup le_sup_left
      hc.normal_subgroupOf_U_sup hc.not_le_centralizer_H
  exact ⟨H₀, ⟨hc.normal_H, hH₀n, hH₀lt, fun Z hZ hlt hZH => absurd (hmax Z hZ hlt hZH.le) hZH.ne⟩,
    hH₀le⟩

theorem IsPTypeConfig.isFaithfulImageSetup (hc : IsPTypeConfig H J U B F W2)
    (hq : Nat.card ↥B = q) (hchief : IsChiefFactor H H₀)
    (hCU : H ⊓ centralizer (U : Set M) ≤ H₀) {b : M} (hb : b ∈ B) (hb1 : b ≠ 1) :
    IsFaithfulImageSetup H (U ⊔ B) U B H₀ b q where
  isComplement_A := hc.isComplement'_H_sup
  coprime := hc.coprime_natCard_H_sup
  le_U := le_sup_left
  le_B := le_sup_right
  normal_U := hc.normal_subgroupOf_U_sup
  isComplement_B := hc.isComplement'_subgroupOf_U_sup
  prime_q := hq ▸ hc.prime_natCard_B
  card_B := hq
  centralizer_inf_eq_bot := hc.inf_centralizer_U_eq_bot
  isChiefFactor := hchief
  centralizer_U_le := hCU
  isCyclic_centralizer_B := hc.inf_centralizer_B_eq_W2 ▸ hc.isCyclic_W2
  eq_zpowers := (zpowers_eq_of_mem_of_ne_one hc.prime_natCard_B hb hb1).symm
  commutator_centralizes := hc.commutator_U_le_centralizer_H

section Model

variable [H.Normal] [H₀.Normal] {p : ℕ} [Fact p.Prime] [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

noncomputable def IsPTypeConfig.linearModel (hc : IsPTypeConfig H J U B F W2)
    (hq : Nat.card ↥B = q) (hchief : IsChiefFactor H H₀)
    (hCU : H ⊓ centralizer (U : Set M) ≤ H₀) {b : M} (hb : b ∈ B) (hb1 : b ≠ 1)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) : PrimeDimLinearSetup p q V :=
  have := hc.finite
  have := hc.isSolvable
  have hs := hc.isFaithfulImageSetup hq hchief hCU hb hb1
  { ne_char := Ne.symm (hs.ne_q p e Fact.out)
    finrank_eq := hs.finrank_eq p e Fact.out
    A := factorLinearImage p H H₀ U e
    b := factorLinearAut p H H₀ e b
    A_ne_bot := hs.factorLinearImage_U_ne_bot p e Fact.out
    isMulCommutative_A := hs.isMulCommutative_factorLinearImage_U p e
    orderOf_b := hs.orderOf_factorLinearAut_b p e Fact.out
    b_mem_normalizer := hs.mem_normalizer_factorLinearImage p e
    isIrreducible_sup := by
      rw [← hs.factorLinearImage_A_eq p e]; exact hs.isIrreducible_factorLinearImage_A p e
    inf_centralizer_b := hs.inf_centralizer_eq_bot p e
    finrank_invariants := hs.finrank_invariants p e }

theorem IsPTypeConfig.linearModel_A (hc : IsPTypeConfig H J U B F W2)
    (hq : Nat.card ↥B = q) (hchief : IsChiefFactor H H₀)
    (hCU : H ⊓ centralizer (U : Set M) ≤ H₀) {b : M} (hb : b ∈ B) (hb1 : b ≠ 1)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    (hc.linearModel hq hchief hCU hb hb1 e).A = factorLinearImage p H H₀ U e := (rfl)

theorem IsPTypeConfig.linearModel_b (hc : IsPTypeConfig H J U B F W2)
    (hq : Nat.card ↥B = q) (hchief : IsChiefFactor H H₀)
    (hCU : H ⊓ centralizer (U : Set M) ≤ H₀) {b : M} (hb : b ∈ B) (hb1 : b ≠ 1)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    (hc.linearModel hq hchief hCU hb hb1 e).b = factorLinearAut p H H₀ e b := (rfl)

end Model

theorem IsPTypeConfig.exists_linearModel (hc : IsPTypeConfig H J U B F W2)
    (hq : Nat.card ↥B = q) :
    ∃ (_ : H.Normal) (H₀ : Subgroup M) (_ : H₀.Normal) (p : ℕ) (_ : Fact p.Prime)
      (_ : Fact q.Prime) (b : M)
      (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative (Fin q → ZMod p)),
      p ≠ q ∧ IsChiefFactor H H₀ ∧ H ⊓ centralizer (U : Set M) ≤ H₀ ∧
      b ∈ B ∧ b ≠ 1 ∧ zpowers b = B ∧
      Nonempty ((↥U ⧸ actionKernel p H H₀ U e) ≃* factorLinearImage p H H₀ U e) ∧
      ∃ D : PrimeDimLinearSetup p q (Fin q → ZMod p),
        D.A = factorLinearImage p H H₀ U e ∧ D.b = factorLinearAut p H H₀ e b ∧
        D.A ≠ ⊥ ∧ IsMulCommutative ↥D.A ∧ orderOf D.b = q ∧
        D.A ⊓ centralizer {D.b} = ⊥ ∧
        Module.finrank (ZMod p) ↥(Representation.invariants (linearGroupRep (zpowers D.b))) = 1 ∧
        Module.finrank (ZMod p) (Fin q → ZMod p) = q ∧
        Xor (ActsReducibly D.A) ((linearGroupRep D.A).IsIrreducible) := by
  have := hc.finite
  have := hc.isSolvable
  have := hc.normal_H
  have hfq := Fact.mk (hq ▸ hc.prime_natCard_B : q.Prime)
  obtain ⟨H₀, hchief, hCU⟩ := hc.exists_isChiefFactor
  have := hchief.normal_den
  obtain ⟨b, hbB, hb1, hbgen⟩ := exists_zpowers_eq_of_prime_natCard hc.prime_natCard_B
  have hs := hc.isFaithfulImageSetup hq hchief hCU hbB hb1
  obtain ⟨p, d, hp, -, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hfp := Fact.mk hp
  have hdq : d = q := by
    have h := hs.finrank_eq p e hp
    rwa [Module.finrank_fin_fun] at h
  subst hdq
  refine ⟨hc.normal_H, H₀, hchief.normal_den, p, hfp, hfq, b, e, hs.ne_q p e hp, hchief, hCU,
    hbB, hb1, hbgen, ⟨quotientActionKernelMulEquiv p e⟩,
    hc.linearModel hq hchief hCU hbB hb1 e, hc.linearModel_A hq hchief hCU hbB hb1 e,
    hc.linearModel_b hq hchief hCU hbB hb1 e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).A_ne_bot
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).isMulCommutative_A
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).orderOf_b
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).inf_centralizer_b
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).finrank_invariants
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).finrank_eq
  · exact (hc.linearModel hq hchief hCU hbB hb1 e).xor_actsReducibly_isIrreducible

end

end CFSG.FeitThompson
