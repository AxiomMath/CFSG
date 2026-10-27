module

public import CFSG.FeitThompson.Definitions.AdmissibleCoprimeActionQuadruple
public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Representations.MinimalActionPrimeGroupElementary
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {G : Type u} [Group G] [Finite G]

def fittingRawPreimage (X : Type*) [Group X] [Finite X] : Subgroup X :=
  haveI := fittingRaw_normal X
  Subgroup.comap (QuotientGroup.mk' (fittingRaw X)) (fittingRaw (X ⧸ fittingRaw X))

theorem mem_fittingRawPreimage_iff {X : Type*} [Group X] [Finite X] {x : X} :
    haveI := fittingRaw_normal X
    x ∈ fittingRawPreimage X ↔
      (QuotientGroup.mk x : X ⧸ fittingRaw X) ∈ fittingRaw (X ⧸ fittingRaw X) := Iff.rfl

instance fittingRawPreimage_normal (X : Type*) [Group X] [Finite X] :
    (fittingRawPreimage X).Normal :=
  haveI := fittingRaw_normal X
  Subgroup.normal_comap _

theorem fittingRaw_le_fittingRawPreimage (X : Type*) [Group X] [Finite X] :
    fittingRaw X ≤ fittingRawPreimage X := by
  have := fittingRaw_normal X
  intro x hx
  rw [mem_fittingRawPreimage_iff, (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

theorem map_mk'_fittingRawPreimage (X : Type*) [Group X] [Finite X] :
    haveI := fittingRaw_normal X
    (fittingRawPreimage X).map (QuotientGroup.mk' (fittingRaw X))
      = fittingRaw (X ⧸ fittingRaw X) := by
  have := fittingRaw_normal X
  rw [fittingRawPreimage,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

omit [Finite G] in
private theorem map_subtype_top (K : Subgroup G) : (⊤ : Subgroup ↥K).map K.subtype = K := by
  rw [← Subgroup.top_subgroupOf (H := K), Subgroup.subgroupOf_map_subtype, top_inf_eq]

omit [Finite G] in
private theorem map_subtype_commutator (K : Subgroup G) :
    (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
  rw [commutator_def, Subgroup.map_commutator, map_subtype_top]

structure IsReducedPrimeCentralizerKernel (p q : ℕ) (H R R0 V K U N P : Subgroup G) : Prop where
  admissible : IsAdmissibleCoprimeActionQuadruple G H R R0
  prime_p : p.Prime
  not_hasPLengthLeOne : ¬ HasPLengthLeOne p ↥⁅H, R⁆
  minimal : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
      HasPLengthLeOne p ↥⁅J, A⁆
  V_eq : V = (fittingRaw ↥H).map H.subtype
  K_le_H : K ≤ H
  R_le_normalizer_K : R ≤ normalizer (K : Set G)
  U_eq : U = V ⊔ K
  N_eq : N = normalizer (K : Set G) ⊓ H
  P_le_N : P ≤ N
  card_P : Nat.card ↥P = p ^ (Nat.card ↥N).factorization p
  R_le_normalizer_P : R ≤ normalizer (P : Set G)
  U_subgroupOf_eq : U.subgroupOf H = fittingRawPreimage ↥H
  inf_K_V : K ⊓ V = ⊥
  coprime_card_K : (Nat.card ↥K).Coprime p
  sup_V_N : V ⊔ N = H
  commutator_K_P_ne_bot : ⁅K, P⁆ ≠ ⊥
  inf_V_centralizer_K : V ⊓ centralizer (K : Set G) = ⊥
  inf_V_N : V ⊓ N = ⊥
  K_eq_fittingRaw_N : K = (fittingRaw ↥N).map N.subtype
  inf_H_centralizer_K_le : H ⊓ centralizer (K : Set G) ≤ K
  sup_V_K_P : V ⊔ K ⊔ P = H
  R_eq : R = R0
  P_eq_commutator : P = ⁅P, R⁆
  P_ne_bot : P ≠ ⊥
  K_eq_commutator : K = ⁅K, P⁆
  prime_q : q.Prime
  odd_q : Odd q
  q_ne_p : q ≠ p
  q_ne_r : q ≠ Nat.card ↥R0
  isPGroup_K : IsPGroup q ↥K
  centralizes_of_lt : ∀ S : Subgroup G, S ≤ K → S ≠ K → P ≤ normalizer (S : Set G) →
    R ≤ normalizer (S : Set G) → P ≤ centralizer (S : Set G)

namespace IsReducedPrimeCentralizerKernel

variable {p q : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P)

include hc

theorem P_le_normalizer_K : P ≤ normalizer (K : Set G) :=
  hc.P_le_N.trans (hc.N_eq ▸ inf_le_left)

theorem sup_le_normalizer_K : P ⊔ R ≤ normalizer (K : Set G) :=
  sup_le hc.P_le_normalizer_K hc.R_le_normalizer_K

def action : ↥(P ⊔ R) →* MulAut ↥K := conjOnNormalized K hc.sup_le_normalizer_K

theorem coe_action_apply (g : ↥(P ⊔ R)) (x : ↥K) :
    ((hc.action g x : ↥K) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
  conjOnNormalized_apply_coe _ _ _

theorem K_ne_bot : K ≠ ⊥ := hc.K_eq_commutator ▸ hc.commutator_K_P_ne_bot

theorem not_dvd_natCard_sup : ¬ q ∣ Nat.card ↥(P ⊔ R) := by
  intro hdvd
  have hmul := natCard_sup_mul_natCard_inf_of_le_normalizer (S := P) (T := R) hc.R_le_normalizer_P
  have hdvd' : q ∣ Nat.card ↥P * Nat.card ↥R := hmul ▸ hdvd.mul_right _
  rcases (Nat.Prime.dvd_mul hc.prime_q).1 hdvd' with h1 | h2
  · exact hc.q_ne_p ((Nat.prime_dvd_prime_iff_eq hc.prime_q hc.prime_p).1
      (hc.prime_q.dvd_of_dvd_pow (hc.card_P ▸ h1)))
  · refine hc.q_ne_r ((Nat.prime_dvd_prime_iff_eq hc.prime_q hc.admissible.prime_card).1 ?_)
    rwa [hc.R_eq] at h2

theorem le_normalizer_map_subtype {S : Subgroup ↥K} (hS : IsInvariantSubgroup hc.action S) :
    P ⊔ R ≤ normalizer ((S.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro g hg s ⟨x, hx, rfl⟩
  exact ⟨hc.action ⟨g, hg⟩ x, hS.apply_mem ⟨g, hg⟩ hx, by
    simpa using hc.coe_action_apply ⟨g, hg⟩ x⟩

theorem isMinimalInvariantAction :
    IsMinimalInvariantAction q hc.action (P.subgroupOf (P ⊔ R)) where
  prime := hc.prime_q
  odd := hc.odd_q
  nontrivial := (Subgroup.nontrivial_iff_ne_bot K).2 hc.K_ne_bot
  isPGroup := hc.isPGroup_K
  coprime := ((Nat.Prime.coprime_iff_not_dvd hc.prime_q).2 hc.not_dvd_natCard_sup).symm
  normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le le_normalizer hc.R_le_normalizer_P)
  actionCommutator_ne_bot := by
    intro hbot
    refine hc.commutator_K_P_ne_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdmem : d ∈ P ⊔ R := (le_sup_left : P ≤ P ⊔ R) hd
    have h1 : hc.action ⟨d, hdmem⟩ = 1 :=
      actionCommutator_eq_bot_iff.1 hbot ⟨d, hdmem⟩ (Subgroup.mem_subgroupOf.2 hd)
    have h2 := congrArg (fun f => ((f (⟨x, hx⟩ : ↥K) : ↥K) : G)) h1
    simp only [hc.coe_action_apply] at h2
    have h3 : d * x * d⁻¹ = x := by simpa using h2
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [h3]
  centralizes := by
    intro S hS hStop d hd x hx
    have hne : S.map K.subtype ≠ K := by
      intro hEq
      refine hStop (eq_top_iff.2 fun y _ => ?_)
      have hy : (y : G) ∈ S.map K.subtype := by rw [hEq]; exact y.2
      obtain ⟨z, hz, hzy⟩ := hy
      exact (Subtype.ext hzy : z = y) ▸ hz
    have hnorm := hc.le_normalizer_map_subtype hS
    have hcent := hc.centralizes_of_lt (S.map K.subtype) (Subgroup.map_subtype_le S) hne
      (le_sup_left.trans hnorm) (le_sup_right.trans hnorm)
    have hdP : (d : G) ∈ P := Subgroup.mem_subgroupOf.1 hd
    have h3 : (x : G) * (d : G) = (d : G) * (x : G) :=
      (Subgroup.mem_centralizer_iff.1 (hcent hdP)) _ ⟨x, hx, rfl⟩
    refine Subtype.ext ?_
    rw [hc.coe_action_apply, ← h3]
    group

theorem pow_eq_one {x : G} (hx : x ∈ K) : x ^ q = 1 := by
  have h := hc.isMinimalInvariantAction.pow_eq_one (⟨x, hx⟩ : ↥K)
  simpa using congrArg (Subtype.val) h

theorem commutator_le_center : ⁅K, K⁆ ≤ K ⊓ centralizer (K : Set G) := by
  have h2 := Subgroup.map_mono (f := K.subtype)
    hc.isMinimalInvariantAction.commutator_le_center
  rwa [map_subtype_commutator, map_center_subtype_eq_inf_centralizer] at h2

theorem invariant_quotient_eq_bot_or_eq_top {S : Subgroup (↥K ⧸ frattini ↥K)}
    (hS : IsInvariantSubgroup (frattiniQuotientAction hc.action) S) : S = ⊥ ∨ S = ⊤ :=
  hc.isMinimalInvariantAction.invariant_quotient_eq_bot_or_eq_top hS

theorem isIrreducible [Fact q.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod q) W]
    (e : (↥K ⧸ frattini ↥K) ≃* Multiplicative W) :
    (representationOfMulAut q (frattiniQuotientAction hc.action) e).IsIrreducible :=
  hc.isMinimalInvariantAction.isIrreducible_representationOfMulAut_frattiniQuotientAction e

theorem actionCentralizer_eq_bot :
    actionCentralizer (frattiniQuotientAction hc.action) (P.subgroupOf (P ⊔ R)) = ⊥ :=
  hc.isMinimalInvariantAction.actionCentralizer_frattiniQuotientAction_eq_bot

theorem mem_frattini_of_forall_conj_mk_eq (x : ↥K)
    (h : ∀ d ∈ P.subgroupOf (P ⊔ R),
      (QuotientGroup.mk (hc.action d x) : ↥K ⧸ frattini ↥K) = QuotientGroup.mk x) :
    x ∈ frattini ↥K := by
  have hmem : (QuotientGroup.mk x : ↥K ⧸ frattini ↥K)
      ∈ actionCentralizer (frattiniQuotientAction hc.action) (P.subgroupOf (P ⊔ R)) :=
    mem_actionCentralizer_frattiniQuotientAction_iff.2 h
  rw [hc.actionCentralizer_eq_bot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).1 hmem

theorem elementaryAbelian_or_special :
    (∃ d : ℕ, 1 ≤ d ∧ Nonempty (↥K ≃* (Fin d → Multiplicative (ZMod q))))
      ∨ (Subgroup.center ↥K = commutator ↥K ∧ commutator ↥K = frattini ↥K) :=
  hc.isMinimalInvariantAction.exists_mulEquiv_pi_or_center_eq_commutator

theorem reducedPrimeCentralizerKernel :
    (∀ x ∈ K, x ^ q = 1) ∧ ⁅K, K⁆ ≤ K ⊓ centralizer (K : Set G) ∧
      (∀ S : Subgroup (↥K ⧸ frattini ↥K),
        IsInvariantSubgroup (frattiniQuotientAction hc.action) S → S = ⊥ ∨ S = ⊤) ∧
      actionCentralizer (frattiniQuotientAction hc.action) (P.subgroupOf (P ⊔ R)) = ⊥ ∧
      ((∃ d : ℕ, 1 ≤ d ∧ Nonempty (↥K ≃* (Fin d → Multiplicative (ZMod q))))
        ∨ (Subgroup.center ↥K = commutator ↥K ∧ commutator ↥K = frattini ↥K)) :=
  ⟨fun _ hx => hc.pow_eq_one hx, hc.commutator_le_center,
    fun _ hS => hc.invariant_quotient_eq_bot_or_eq_top hS, hc.actionCentralizer_eq_bot,
    hc.elementaryAbelian_or_special⟩

end IsReducedPrimeCentralizerKernel

end CFSG.FeitThompson
