module

public import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
public import CFSG.FeitThompson.Local.OddCriticalExponentSubgroup
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
import CFSG.FeitThompson.Local.InvariantCyclicComplementPrimeLine
import CFSG.FeitThompson.Local.AutomorphismsFixingPlaneQuotientAbelian
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {q : ℕ} {K A : Type*} [Group K] [Group A]

def actionCommutator (ρ : A →* MulAut K) (D : Subgroup A) : Subgroup K :=
  Subgroup.closure {y : K | ∃ x : K, ∃ d ∈ D, x⁻¹ * ρ d x = y}

theorem actionCommutator_eq_closure (ρ : A →* MulAut K) (D : Subgroup A) :
    actionCommutator ρ D = Subgroup.closure {y : K | ∃ x : K, ∃ d ∈ D, x⁻¹ * ρ d x = y} := (rfl)

theorem inv_mul_apply_mem_actionCommutator (ρ : A →* MulAut K) {D : Subgroup A} {d : A}
    (hd : d ∈ D) (x : K) : x⁻¹ * ρ d x ∈ actionCommutator ρ D :=
  Subgroup.subset_closure ⟨x, d, hd, rfl⟩

theorem actionCommutator_le {ρ : A →* MulAut K} {D : Subgroup A} {H : Subgroup K}
    (h : ∀ d ∈ D, ∀ x : K, x⁻¹ * ρ d x ∈ H) : actionCommutator ρ D ≤ H := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro y ⟨x, d, hd, rfl⟩
  exact h d hd x

theorem actionCommutator_eq_bot_iff {ρ : A →* MulAut K} {D : Subgroup A} :
    actionCommutator ρ D = ⊥ ↔ ∀ d ∈ D, ρ d = 1 := by
  refine ⟨fun h d hd => ?_, fun h => le_bot_iff.1 (actionCommutator_le fun d hd x => ?_)⟩
  · ext x
    have hx := h ▸ inv_mul_apply_mem_actionCommutator ρ hd x
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hx
    simpa using hx.symm
  · rw [h d hd]; simp

def actionCentralizer (ρ : A →* MulAut K) (D : Subgroup A) : Subgroup K :=
  ⨅ d : ↥D, ((ρ (d : A) : K ≃* K) : K →* K).eqLocus (MonoidHom.id K)

theorem mem_actionCentralizer {ρ : A →* MulAut K} {D : Subgroup A} {x : K} :
    x ∈ actionCentralizer ρ D ↔ ∀ d ∈ D, ρ d x = x := by
  simp only [actionCentralizer, Subgroup.mem_iInf, Subtype.forall]
  rfl

theorem actionCentralizer_eq_top_iff {ρ : A →* MulAut K} {D : Subgroup A} :
    actionCentralizer ρ D = ⊤ ↔ ∀ d ∈ D, ρ d = 1 := by
  rw [eq_top_iff']
  refine ⟨fun h d hd => ?_, fun h x => mem_actionCentralizer.2 fun d hd => by rw [h d hd]; rfl⟩
  ext x
  exact mem_actionCentralizer.1 (h x) d hd

theorem le_actionCentralizer {ρ : A →* MulAut K} {D : Subgroup A} {H : Subgroup K}
    (h : ∀ d ∈ D, ∀ x ∈ H, ρ d x = x) : H ≤ actionCentralizer ρ D :=
  fun x hx => mem_actionCentralizer.2 fun d hd => h d hd x hx

private theorem isInvariantSubgroup_of_forall_apply_mem (ρ : A →* MulAut K) (N : Subgroup K)
    (h : ∀ b : A, ∀ v ∈ N, ρ b v ∈ N) : IsInvariantSubgroup ρ N :=
  isInvariantSubgroup_iff_forall_map_eq.2 fun b => le_antisymm
    (by rintro x ⟨v, hv, rfl⟩; exact h b v hv)
    (fun v hv => ⟨ρ b⁻¹ v, h b⁻¹ v hv, by
      change ρ b (ρ b⁻¹ v) = v
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩)

theorem isInvariantSubgroup_actionCentralizer (ρ : A →* MulAut K) (D : Subgroup A) [D.Normal] :
    IsInvariantSubgroup ρ (actionCentralizer ρ D) := by
  refine isInvariantSubgroup_of_forall_apply_mem ρ _ fun a x hx => ?_
  rw [mem_actionCentralizer] at hx ⊢
  intro d hd
  have hd' : a⁻¹ * d * a ∈ D := by simpa using ‹D.Normal›.conj_mem d hd a⁻¹
  have hcalc : ρ d (ρ a x) = ρ a (ρ (a⁻¹ * d * a) x) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hcalc, hx _ hd']

theorem isInvariantSubgroup_actionCommutator (ρ : A →* MulAut K) (D : Subgroup A) [D.Normal] :
    IsInvariantSubgroup ρ (actionCommutator ρ D) := by
  refine isInvariantSubgroup_of_forall_apply_mem ρ _ fun a => ?_
  have hle : actionCommutator ρ D ≤ (actionCommutator ρ D).comap ((ρ a : K ≃* K) : K →* K) := by
    refine actionCommutator_le fun d hd x => ?_
    rw [Subgroup.mem_comap]
    have hd' : a * d * a⁻¹ ∈ D := ‹D.Normal›.conj_mem d hd a
    have hcalc : (ρ a) (x⁻¹ * ρ d x) = (ρ a x)⁻¹ * ρ (a * d * a⁻¹) (ρ a x) := by
      rw [map_mul, map_inv]
      congr 1
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    change (ρ a) (x⁻¹ * ρ d x) ∈ actionCommutator ρ D
    rw [hcalc]
    exact inv_mul_apply_mem_actionCommutator ρ hd' _
  exact fun x hx => hle hx

def frattiniQuotientAction (ρ : A →* MulAut K) : A →* MulAut (K ⧸ frattini K) :=
  (frattiniQuotientAut K).comp ρ

@[simp]
theorem frattiniQuotientAction_mk (ρ : A →* MulAut K) (a : A) (x : K) :
    frattiniQuotientAction ρ a (QuotientGroup.mk x)
      = (QuotientGroup.mk (ρ a x) : K ⧸ frattini K) :=
  frattiniQuotientAut_apply_mk _ _

theorem mem_actionCentralizer_frattiniQuotientAction_iff {ρ : A →* MulAut K} {D : Subgroup A}
    {x : K} :
    (QuotientGroup.mk x : K ⧸ frattini K) ∈ actionCentralizer (frattiniQuotientAction ρ) D
      ↔ ∀ d ∈ D, (QuotientGroup.mk (ρ d x) : K ⧸ frattini K) = QuotientGroup.mk x := by
  rw [mem_actionCentralizer]
  exact forall₂_congr fun _ _ => by rw [frattiniQuotientAction_mk]

theorem frattiniQuotientAction_eq_one_iff {ρ : A →* MulAut K} {a : A} :
    frattiniQuotientAction ρ a = 1 ↔ ρ a ∈ autKerFrattini K := by
  rw [autKerFrattini_eq_ker, MonoidHom.mem_ker]
  rfl

theorem map_actionCommutator (ρ : A →* MulAut K) (D : Subgroup A) :
    (actionCommutator ρ D).map (QuotientGroup.mk' (frattini K))
      = actionCommutator (frattiniQuotientAction ρ) D := by
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨-, ⟨x, d, hd, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk x, d, hd, by rw [frattiniQuotientAction_mk]; simp⟩
  · rintro ⟨z, d, hd, rfl⟩
    induction z using QuotientGroup.induction_on with
    | H x => exact ⟨x⁻¹ * ρ d x, ⟨x, d, hd, rfl⟩, by rw [frattiniQuotientAction_mk]; simp⟩

theorem isInvariantSubgroup_map_mk_of_characteristic (ρ : A →* MulAut K) (N : Subgroup K)
    [N.Characteristic] :
    IsInvariantSubgroup (frattiniQuotientAction ρ) (N.map (QuotientGroup.mk' (frattini K))) := by
  refine isInvariantSubgroup_of_forall_apply_mem _ _ ?_
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨ρ a y, ?_, ?_⟩
  · exact (Subgroup.characteristic_iff_map_eq.1 ‹N.Characteristic› (ρ a)) ▸ ⟨y, hy, rfl⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, frattiniQuotientAction_mk]

theorem isInvariantSubgroup_comap_mk {ρ : A →* MulAut K} {S : Subgroup (K ⧸ frattini K)}
    (hS : IsInvariantSubgroup (frattiniQuotientAction ρ) S) :
    IsInvariantSubgroup ρ (S.comap (QuotientGroup.mk' (frattini K))) := by
  refine isInvariantSubgroup_of_forall_apply_mem ρ _ fun a x hx => ?_
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hx ⊢
  rw [← frattiniQuotientAction_mk ρ a x]
  exact hS.apply_mem a hx

theorem comap_mk_eq_top_iff {S : Subgroup (K ⧸ frattini K)} :
    S.comap (QuotientGroup.mk' (frattini K)) = ⊤ ↔ S = ⊤ := by
  refine ⟨fun h => ?_, fun h => by rw [h, Subgroup.comap_top]⟩
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (frattini K)) S, h]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem comap_sup_comap_eq_top {S T : Subgroup (K ⧸ frattini K)} (h : S ⊔ T = ⊤) :
    S.comap (QuotientGroup.mk' (frattini K)) ⊔ T.comap (QuotientGroup.mk' (frattini K)) = ⊤ := by
  set f := QuotientGroup.mk' (frattini K) with hf
  have hker : f.ker ≤ S.comap f ⊔ T.comap f := le_sup_left.trans' (Subgroup.ker_le_comap f S)
  have hcm := Subgroup.comap_map_eq f (S.comap f ⊔ T.comap f)
  rw [sup_eq_left.2 hker] at hcm
  rw [← hcm, Subgroup.map_sup,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), h,
    Subgroup.comap_top]

theorem eq_top_of_map_mk_eq_top [Finite K] {S : Subgroup K}
    (h : S.map (QuotientGroup.mk' (frattini K)) = ⊤) : S = ⊤ := by
  refine frattini_nongenerating (K := S) ?_
  have hmapsup : (S ⊔ frattini K).map (QuotientGroup.mk' (frattini K)) = ⊤ := by
    rw [Subgroup.map_sup, h, top_sup_eq]
  have hker : (QuotientGroup.mk' (frattini K)).ker ≤ S ⊔ frattini K := by
    rw [QuotientGroup.ker_mk']; exact le_sup_right
  have hcm := Subgroup.comap_map_eq_self hker
  rw [hmapsup, Subgroup.comap_top] at hcm
  exact hcm.symm

theorem exists_invariant_isCompl_of_isMulCommutative {R : Type*} [Group R] [Finite A]
    (hcomm : IsMulCommutative R) (hq : q.Prime) (hexp : ∀ x : R, x ^ q = 1) (β : A →* MulAut R)
    (hA : ¬ q ∣ Nat.card A) {S : Subgroup R} (hS : ∀ b : A, ∀ x ∈ S, β b x ∈ S) :
    ∃ T : Subgroup R, (∀ b : A, ∀ x ∈ T, β b x ∈ T) ∧ IsCompl S T := by
  have := hcomm
  let _ : CommGroup R := IsMulCommutative.instCommGroup
  exact exists_invariant_isCompl_of_pow_eq_one hq hexp β hA hS

theorem nontrivial_quotient_frattini (K : Type*) [Group K] [Finite K] [Nontrivial K] :
    Nontrivial (K ⧸ frattini K) := by
  refine QuotientGroup.nontrivial_iff.2 fun hc => ?_
  have : IsCoatomic (Subgroup K) := Finite.to_isCoatomic
  rcases eq_top_or_exists_le_coatom (⊥ : Subgroup K) with hb | ⟨M, hM, -⟩
  · exact absurd hb (by simp)
  · exact hM.1 (top_le_iff.1 (hc ▸ frattini_le_coatom hM))

structure IsMinimalInvariantAction (q : ℕ) (ρ : A →* MulAut K) (D : Subgroup A) : Prop where
  prime : q.Prime
  odd : Odd q
  nontrivial : Nontrivial K
  isPGroup : IsPGroup q K
  coprime : (Nat.card A).Coprime q
  normal : D.Normal
  actionCommutator_ne_bot : actionCommutator ρ D ≠ ⊥
  centralizes : ∀ H : Subgroup K, IsInvariantSubgroup ρ H → H ≠ ⊤ → ∀ d ∈ D, ∀ x ∈ H, ρ d x = x

namespace IsMinimalInvariantAction

variable [Finite K] [Finite A] {ρ : A →* MulAut K} {D : Subgroup A}
  (h : IsMinimalInvariantAction q ρ D)

include h

omit [Finite K] [Finite A] in
theorem exists_mem_apply_ne_one : ∃ d ∈ D, ρ d ≠ 1 := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact h.actionCommutator_ne_bot (actionCommutator_eq_bot_iff.2 hc)

omit [Finite K] [Finite A] in
theorem apply_eq_one_of_mem_isPGroup {S : Subgroup (MulAut K)} (hS : IsPGroup q S) {a : A}
    (ha : ρ a ∈ S) : ρ a = 1 := by
  have := Fact.mk h.prime
  have hcop : (orderOf (ρ a)).Coprime q :=
    Nat.Coprime.coprime_dvd_left ((orderOf_map_dvd ρ a).trans (orderOf_dvd_natCard a)) h.coprime
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hS (⟨ρ a, ha⟩ : S)
  have hk' : orderOf (ρ a) = q ^ k := by
    rw [← hk]; exact Subgroup.orderOf_coe (⟨ρ a, ha⟩ : S)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk'; exact orderOf_eq_one_iff.1 hk'
  · exact absurd (Nat.Coprime.eq_one_of_dvd hcop.symm (hk' ▸ dvd_pow_self q hkpos.ne'))
      h.prime.one_lt.ne'

omit [Finite K] [Finite A] in
theorem eq_top_of_isOddCriticalExponentSubgroup {H : Subgroup K}
    (hH : IsOddCriticalExponentSubgroup q H) : H = ⊤ := by
  by_contra hne
  obtain ⟨d, hd, hdne⟩ := h.exists_mem_apply_ne_one
  have := hH.characteristic
  refine hdne (h.apply_eq_one_of_mem_isPGroup hH.isPGroup_fixingSubgroup (a := d) ?_)
  rw [mem_fixingSubgroup_iff]
  intro y hy
  rw [MulAut.smul_def]
  exact h.centralizes H (isInvariantSubgroup_of_characteristic ρ H) hne d hd y hy

omit [Finite A] in
theorem pow_eq_one (x : K) : x ^ q = 1 := by
  have := h.nontrivial
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup h.prime h.odd h.isPGroup
  exact hH.pow_eq_one x (h.eq_top_of_isOddCriticalExponentSubgroup hH ▸ Subgroup.mem_top x)

omit [Finite A] in
theorem commutator_le_center : commutator K ≤ Subgroup.center K := by
  have := h.nontrivial
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup h.prime h.odd h.isPGroup
  have h1 := hH.commutator_self_le_center
  rw [h.eq_top_of_isOddCriticalExponentSubgroup hH, map_center_subtype_eq_inf_centralizer] at h1
  rw [commutator_def]
  simpa [Subgroup.centralizer_univ] using h1

omit [Finite A] in
theorem frattini_eq_commutator : frattini K = commutator K := by
  rw [frattini_eq_commutatorSupPowClosure_of_isPGroup h.prime h.isPGroup]
  refine le_antisymm (commutatorSupPowClosure_le.2 ⟨le_rfl, fun x => ?_⟩)
    commutator_le_commutatorSupPowClosure
  rw [h.pow_eq_one x]; exact one_mem _

omit [Finite A] in
theorem frattini_le_center : frattini K ≤ Subgroup.center K :=
  h.frattini_eq_commutator ▸ h.commutator_le_center

omit [Finite A] in
theorem isMulCommutative_quotient : IsMulCommutative (K ⧸ frattini K) := by
  have := Fact.mk h.prime
  obtain ⟨n, hn⟩ := h.isPGroup.exists_card_eq
  exact isMulCommutative_quotient_frattini (n := n) h.prime hn

omit [Finite A] in
theorem pow_eq_one_quotient (x : K ⧸ frattini K) : x ^ q = 1 := by
  induction x using QuotientGroup.induction_on with
  | H y => rw [← QuotientGroup.mk_pow, h.pow_eq_one y, QuotientGroup.mk_one]

omit [Finite A] in
theorem exists_mem_frattiniQuotientAction_ne_one :
    ∃ d ∈ D, frattiniQuotientAction ρ d ≠ 1 := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  obtain ⟨d, hd, hdne⟩ := h.exists_mem_apply_ne_one
  exact hdne (h.apply_eq_one_of_mem_isPGroup
    (isPGroup_autKerFrattini_of_isPGroup h.prime h.isPGroup)
    (frattiniQuotientAction_eq_one_iff.1 (hc d hd)))

theorem invariant_quotient_eq_bot_or_eq_top {S : Subgroup (K ⧸ frattini K)}
    (hS : IsInvariantSubgroup (frattiniQuotientAction ρ) S) : S = ⊥ ∨ S = ⊤ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hSbot, hStop⟩ := hcon
  obtain ⟨T, hT, hcompl⟩ := exists_invariant_isCompl_of_isMulCommutative
    h.isMulCommutative_quotient h.prime h.pow_eq_one_quotient (frattiniQuotientAction ρ)
    ((Nat.Prime.coprime_iff_not_dvd h.prime).1 h.coprime.symm) (fun a x hx => hS.apply_mem a hx)
  have hTinv : IsInvariantSubgroup (frattiniQuotientAction ρ) T :=
    isInvariantSubgroup_of_forall_apply_mem _ _ hT
  have hTtop : T ≠ ⊤ := fun hTt => hSbot (by simpa [hTt] using hcompl.inf_eq_bot)
  refine h.actionCommutator_ne_bot (actionCommutator_eq_bot_iff.2 ?_)
  rw [← actionCentralizer_eq_top_iff, eq_top_iff, ← comap_sup_comap_eq_top hcompl.sup_eq_top]
  exact sup_le
    (le_actionCentralizer fun d hd x hx => h.centralizes _ (isInvariantSubgroup_comap_mk hS)
      (fun hc2 => hStop (comap_mk_eq_top_iff.1 hc2)) d hd x hx)
    (le_actionCentralizer fun d hd x hx => h.centralizes _ (isInvariantSubgroup_comap_mk hTinv)
      (fun hc2 => hTtop (comap_mk_eq_top_iff.1 hc2)) d hd x hx)

theorem isIrreducible_representationOfMulAut_frattiniQuotientAction [Fact q.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod q) V] (e : (K ⧸ frattini K) ≃* Multiplicative V) :
    (representationOfMulAut q (frattiniQuotientAction ρ) e).IsIrreducible := by
  have := h.nontrivial
  have := nontrivial_quotient_frattini K
  exact isIrreducible_representationOfMulAut q _ e fun S hS =>
    h.invariant_quotient_eq_bot_or_eq_top (isInvariantSubgroup_of_forall_apply_mem _ _ hS)

theorem actionCentralizer_frattiniQuotientAction_eq_bot :
    actionCentralizer (frattiniQuotientAction ρ) D = ⊥ := by
  have := h.normal
  rcases h.invariant_quotient_eq_bot_or_eq_top
    (isInvariantSubgroup_actionCentralizer (frattiniQuotientAction ρ) D) with hb | ht
  · exact hb
  · obtain ⟨d, hd, hdne⟩ := h.exists_mem_frattiniQuotientAction_ne_one
    exact absurd (actionCentralizer_eq_top_iff.1 ht d hd) hdne

theorem actionCommutator_eq_top : actionCommutator ρ D = ⊤ := by
  have := h.normal
  refine eq_top_of_map_mk_eq_top ?_
  rw [map_actionCommutator]
  rcases h.invariant_quotient_eq_bot_or_eq_top
    (isInvariantSubgroup_actionCommutator (frattiniQuotientAction ρ) D) with hb | ht
  · obtain ⟨d, hd, hdne⟩ := h.exists_mem_frattiniQuotientAction_ne_one
    exact absurd (actionCommutator_eq_bot_iff.1 hb d hd) hdne
  · exact ht

theorem isMulCommutative_or_center_eq_commutator :
    IsMulCommutative K ∨ (Subgroup.center K = commutator K ∧ commutator K = frattini K) := by
  rcases h.invariant_quotient_eq_bot_or_eq_top
    (isInvariantSubgroup_map_mk_of_characteristic ρ (Subgroup.center K)) with hb | ht
  · right
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    have hZ : Subgroup.center K = frattini K := le_antisymm hb h.frattini_le_center
    exact ⟨by rw [hZ, h.frattini_eq_commutator], h.frattini_eq_commutator.symm⟩
  · left
    exact Subgroup.center_eq_top_iff.1 (eq_top_of_map_mk_eq_top ht)

theorem exists_mulEquiv_pi_or_center_eq_commutator :
    (∃ d : ℕ, 1 ≤ d ∧ Nonempty (K ≃* (Fin d → Multiplicative (ZMod q))))
      ∨ (Subgroup.center K = commutator K ∧ commutator K = frattini K) := by
  rcases h.isMulCommutative_or_center_eq_commutator with hcomm | hspecial
  · refine Or.inl ?_
    have := hcomm
    have := h.nontrivial
    let _ : CommGroup K := IsMulCommutative.instCommGroup
    obtain ⟨d, hcard, he⟩ := exists_mulEquiv_pi_multiplicative_zmod h.prime K h.pow_eq_one
    refine ⟨d, ?_, he⟩
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [pow_zero, Nat.card_eq_one_iff_unique] at hcard
      exact absurd hcard.1 (not_subsingleton_iff_nontrivial.2 ‹Nontrivial K›)
    · exact hpos
  · exact Or.inr hspecial

end IsMinimalInvariantAction

end CFSG.FeitThompson
