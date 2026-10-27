module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
import CFSG.FeitThompson.Foundations.CoprimeAutomorphismFaithfulFitting
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.MetacyclicCoprimeActionAbelian
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open scoped commutatorElement

universe u

section Aux

variable {G : Type*} [Group G]

theorem le_normalizer_normalizer_of_le {A K : Subgroup G} (h : A ≤ normalizer (K : Set G)) :
    A ≤ normalizer ((normalizer (K : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have hgK := mem_normalizer_iff_map_conj_eq.1 (h hg)
  rw [mem_normalizer_iff_map_conj_eq,
    Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g : G →* G)) K
      (MulAut.conj g).bijective, hgK]

theorem commutatorElement_mem_centralizer_of_isCyclic {K : Subgroup G} [IsCyclic ↥K]
    {x y : G} (hx : x ∈ normalizer (K : Set G)) (hy : y ∈ normalizer (K : Set G)) :
    ⁅x, y⁆ ∈ centralizer (K : Set G) := by
  set E : Subgroup G := normalizer (K : Set G) with hE
  set φ : ↥E →* MulAut ↥K := conjOnNormalized K (le_refl E) with hφ
  have hmem : ⁅x, y⁆ ∈ E := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hsub : (⟨⁅x, y⁆, hmem⟩ : ↥E) = ⁅(⟨x, hx⟩ : ↥E), (⟨y, hy⟩ : ↥E)⁆ := Subtype.ext rfl
  have h1 : φ ⟨⁅x, y⁆, hmem⟩ = 1 := by
    rw [hsub, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact commute_mulAut_of_isCyclic ↥K _ _
  refine mem_centralizer_iff.2 fun d hd => ?_
  have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨d, hd⟩ : ↥K) : G)) h1
  simp only [hφ, conjOnNormalized_apply_coe] at h2
  have h3 : ⁅x, y⁆ * d * ⁅x, y⁆⁻¹ = d := by simpa using h2
  calc d * ⁅x, y⁆ = (⁅x, y⁆ * d * ⁅x, y⁆⁻¹) * ⁅x, y⁆ := by rw [h3]
    _ = ⁅x, y⁆ * d := by group

theorem commutator_eq_bot_of_commutator_map_fittingRaw_eq_bot [Finite G] {N A : Subgroup G}
    [Group.IsSolvable ↥N] (hA : A ≤ normalizer (N : Set G))
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥N))
    (h : ⁅(fittingRaw ↥N).map N.subtype, A⁆ = ⊥) : ⁅N, A⁆ = ⊥ := by
  set φ : ↥A →* MulAut ↥N := conjOnNormalized N hA with hφ
  have hcentr : (fittingRaw ↥N).map N.subtype ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 h
  have key : ∀ a : ↥A, φ a = 1 := by
    intro a
    have hdvd : Nat.card ↥φ.range ∣ Nat.card ↥A := Subgroup.card_range_dvd φ
    have hcop' : (Nat.card ↥φ.range).Coprime (Nat.card ↥N) := hcop.coprime_dvd_left hdvd
    have hone : (⟨φ a, ⟨a, rfl⟩⟩ : ↥φ.range) = 1 := by
      refine eq_one_of_fixes_fittingRaw φ.range.subtype φ.range.subtype_injective hcop' ?_
      intro x hx
      refine Subtype.ext ?_
      have hxG : (x : G) ∈ (fittingRaw ↥N).map N.subtype := ⟨x, hx, rfl⟩
      have hcomm := mem_centralizer_iff.1 (hcentr hxG) (a : G) a.2
      simp only [coe_subtype, hφ, conjOnNormalized_apply_coe]
      rw [hcomm]
      group
    exact congrArg (Subtype.val) hone
  rw [commutator_eq_bot_iff_le_centralizer]
  intro n hn
  refine mem_centralizer_iff.2 fun a ha => ?_
  have h2 := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : G)) (key ⟨a, ha⟩)
  simp only [hφ, conjOnNormalized_apply_coe] at h2
  have h3 : a * n * a⁻¹ = n := by simpa using h2
  calc a * n = (a * n * a⁻¹) * a := by group
    _ = n * a := by rw [h3]

theorem le_commutator_of_sup_eq_of_inf_eq_bot {V N R H : Subgroup G} [V.Normal]
    (hsup : V ⊔ N = H) (hinf : V ⊓ N = ⊥) (hHR : H = ⁅H, R⁆) (hle : ⁅N, R⁆ ≤ N) :
    N ≤ ⁅N, R⁆ := by
  have hmapH : H.map (QuotientGroup.mk' V) = N.map (QuotientGroup.mk' V) := by
    rw [← hsup, Subgroup.map_sup]
    simp
  have hmapN : N.map (QuotientGroup.mk' V) = (⁅N, R⁆).map (QuotientGroup.mk' V) :=
    calc N.map (QuotientGroup.mk' V) = H.map (QuotientGroup.mk' V) := hmapH.symm
      _ = (⁅H, R⁆).map (QuotientGroup.mk' V) := by rw [← hHR]
      _ = ⁅H.map (QuotientGroup.mk' V), R.map (QuotientGroup.mk' V)⁆ := Subgroup.map_commutator ..
      _ = ⁅N.map (QuotientGroup.mk' V), R.map (QuotientGroup.mk' V)⁆ := by rw [hmapH]
      _ = (⁅N, R⁆).map (QuotientGroup.mk' V) := (Subgroup.map_commutator ..).symm
  intro n hn
  obtain ⟨c, hcmem, hcn⟩ : (QuotientGroup.mk' V) n ∈ (⁅N, R⁆).map (QuotientGroup.mk' V) :=
    hmapN ▸ ⟨n, hn, rfl⟩
  have hvmem : c⁻¹ * n ∈ V := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcn
    exact hcn
  have hmem : c⁻¹ * n ∈ V ⊓ N := ⟨hvmem, mul_mem (N.inv_mem (hle hcmem)) hn⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  rw [show n = c by simpa using (mul_eq_one_iff_eq_inv.1 hmem).symm]
  exact hcmem

end Aux

variable {G : Type u} [Group G] [Finite G]

structure IsPrimeCentralizerKernelSetup (p : ℕ) (H R R0 V K U N P : Subgroup G) : Prop where
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

theorem IsReducedPrimeCentralizerKernel.isPrimeCentralizerKernelSetup {p q : ℕ}
    {H R R0 V K U N P : Subgroup G}
    (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P) :
    IsPrimeCentralizerKernelSetup p H R R0 V K U N P where
  admissible := hc.admissible
  prime_p := hc.prime_p
  not_hasPLengthLeOne := hc.not_hasPLengthLeOne
  minimal := hc.minimal
  V_eq := hc.V_eq
  K_le_H := hc.K_le_H
  R_le_normalizer_K := hc.R_le_normalizer_K
  U_eq := hc.U_eq
  N_eq := hc.N_eq
  P_le_N := hc.P_le_N
  card_P := hc.card_P
  R_le_normalizer_P := hc.R_le_normalizer_P
  U_subgroupOf_eq := hc.U_subgroupOf_eq
  inf_K_V := hc.inf_K_V
  coprime_card_K := hc.coprime_card_K
  sup_V_N := hc.sup_V_N
  commutator_K_P_ne_bot := hc.commutator_K_P_ne_bot
  inf_V_centralizer_K := hc.inf_V_centralizer_K
  inf_V_N := hc.inf_V_N
  K_eq_fittingRaw_N := hc.K_eq_fittingRaw_N
  inf_H_centralizer_K_le := hc.inf_H_centralizer_K_le

namespace IsPrimeCentralizerKernelSetup

variable {p : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerKernelSetup p H R R0 V K U N P)

include hc

theorem le_normalizer_K_of_mem_N : N ≤ normalizer (K : Set G) := by
  rw [hc.N_eq]; exact inf_le_left

theorem N_le_H : N ≤ H := by rw [hc.N_eq]; exact inf_le_right

theorem K_le_N : K ≤ N := by rw [hc.K_eq_fittingRaw_N]; exact map_subtype_le _

theorem R_le_normalizer_N : R ≤ normalizer (N : Set G) := by
  have hHn := hc.admissible.normal
  rw [hc.N_eq]
  exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_normalizer_of_le hc.R_le_normalizer_K hg, le_normalizer_of_normal hg⟩

theorem commutator_R0_ne_bot : ⁅K, R0⁆ ≠ ⊥ := by
  intro h0
  have _iFp : Fact p.Prime := ⟨hc.prime_p⟩
  have hadm := hc.admissible
  have hHn : H.Normal := hadm.normal
  have hsolv : Group.IsSolvable G := hadm.isSolvable
  have hNH : N ≤ H := hc.N_le_H
  have hNnorm : N ≤ normalizer (K : Set G) := hc.le_normalizer_K_of_mem_N
  have hKN : K ≤ N := hc.K_le_N
  have hR0R : R0 ≤ R := hadm.le
  have hcop : (Nat.card ↥R0).Coprime (Nat.card ↥N) :=
    (hadm.coprime.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hR0R)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hNH)
  have hNR0 : ⁅N, R0⁆ = ⊥ := by
    refine commutator_eq_bot_of_commutator_map_fittingRaw_eq_bot
      (hR0R.trans hc.R_le_normalizer_N) hcop ?_
    rw [← hc.K_eq_fittingRaw_N]; exact h0
  have hNC : N ≤ centralizer (R0 : Set G) := commutator_eq_bot_iff_le_centralizer.1 hNR0
  have _iZ : IsZGroup ↥(centralizer (R0 : Set G) ⊓ H) := hadm.isZGroup_centralizer
  have _iZK : IsZGroup ↥K := isZGroup_of_le (le_inf (hKN.trans hNC) (hKN.trans hNH))
  have _iNil : Group.IsNilpotent ↥K := by
    rw [hc.K_eq_fittingRaw_N]; exact isNilpotent_map_fittingRaw N
  have _iCyc : IsCyclic ↥K := inferInstance
  have hNRK : ⁅N, R⁆ ≤ K := by
    refine le_trans (Subgroup.commutator_le.2 fun n hn r hr => ?_) hc.inf_H_centralizer_K_le
    refine Subgroup.mem_inf.2 ⟨?_, commutatorElement_mem_centralizer_of_isCyclic (hNnorm hn)
      (hc.R_le_normalizer_K hr)⟩
    have h1 : ⁅n, r⁆ = n * (r * n⁻¹ * r⁻¹) := by rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hNH hn) (hHn.conj_mem _ (H.inv_mem (hNH hn)) r)
  have _iVn : V.Normal := by rw [hc.V_eq]; exact normal_map_subtype_fittingRaw hHn
  have hNle : N ≤ ⁅N, R⁆ :=
    le_commutator_of_sup_eq_of_inf_eq_bot hc.sup_V_N hc.inf_V_N
      (eq_commutator_of_minimal hadm hc.not_hasPLengthLeOne hc.minimal) (hNRK.trans hKN)
  have hPK : P ≤ K := hc.P_le_N.trans (hNle.trans hNRK)
  rcases Nat.eq_zero_or_pos ((Nat.card ↥N).factorization p) with hk | hk
  · have hone : Nat.card ↥P = 1 := by rw [hc.card_P, hk, pow_zero]
    exact hc.commutator_K_P_ne_bot
      (by rw [Subgroup.card_eq_one.1 hone, Subgroup.commutator_bot_right])
  · have hpP : p ∣ Nat.card ↥P := by rw [hc.card_P]; exact dvd_pow_self p hk.ne'
    exact hc.prime_p.one_lt.ne'
      (hc.coprime_card_K.symm.eq_one_of_dvd (hpP.trans (Subgroup.card_dvd_of_le hPK)))

theorem not_le_centralizer_K : ¬ R0 ≤ centralizer (K : Set G) := by
  intro h
  exact hc.commutator_R0_ne_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      ((Subgroup.mem_centralizer_iff.1 (h hy)) x hx).symm))

end IsPrimeCentralizerKernelSetup

end CFSG.FeitThompson

end
