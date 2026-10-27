module

public import CFSG.FeitThompson.Definitions.AdmissibleCoprimeActionQuadruple
public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
import CFSG.FeitThompson.Local.PrimeCentralizerSpecialFixedLine
import CFSG.FeitThompson.Local.HyperplaneOrbitCountContradiction
import CFSG.FeitThompson.Local.ReducedKernelElementaryRankThree
import CFSG.FeitThompson.Local.CounterexampleReducesToThreePrimes
import CFSG.FeitThompson.Local.PrimeSubgroupFixesFittingLine
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

universe u

theorem isAdmissibleCoprimeActionQuadruple_of_coe_mul_coe {X : Type*} [Group X]
    {H R R0 : Subgroup X} (hsolv : Group.IsSolvable X) (hodd : Odd (Nat.card X)) (hHn : H.Normal)
    (hprod : (H : Set X) * (R : Set X) = Set.univ) (hinf : H ⊓ R = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card R)) (hR0 : R0 ≤ R) (hR0card : (Nat.card R0).Prime)
    (hZ : ∀ t : ℕ, t.Prime →
      ∀ Q : Sylow t (centralizer (R0 : Set X) ⊓ H : Subgroup X), IsCyclic Q) :
    IsAdmissibleCoprimeActionQuadruple X H R R0 where
  isSolvable := hsolv
  odd_card := hodd
  normal := hHn
  sup_eq_top := by
    have := hHn
    have h := Subgroup.normal_mul H R
    rw [hprod] at h
    exact SetLike.coe_injective (h.trans Subgroup.coe_top.symm)
  inf_eq_bot := hinf
  coprime := hcop
  le := hR0
  prime_card := hR0card
  isZGroup_centralizer := (isZGroup_iff _).2 hZ

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G] {H R R0 : Subgroup G}

theorem false_of_not_hasPLengthLeOne_of_minimal
    (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
    (hnot : ¬ HasPLengthLeOne p ↥⁅H, R⁆)
    (hmin : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
      IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
      HasPLengthLeOne p ↥⁅J, A⁆) : False := by
  obtain ⟨K, P, -, hKU, hRK, hVK, hVKbot, hcopK, hVN, hRP, hPN, hcardP, -, hKP⟩ :=
    exists_invariant_complement_sylow_of_minimal hadm hnot hmin
  set V : Subgroup G := (fittingRaw ↥H).map H.subtype with hV
  set U : Subgroup G := (fittingRawPreimage ↥H).map H.subtype with hU
  set N : Subgroup G := normalizer (K : Set G) ⊓ H with hN
  have hcompl : IsPrimeCentralizerComplementSetup p H R R0 V K U N P :=
    { admissible := hadm
      prime_p := Fact.out
      not_hasPLengthLeOne := hnot
      minimal := hmin
      V_eq := rfl
      K_le_H := hKU.trans (Subgroup.map_subtype_le _)
      R_le_normalizer_K := hRK
      U_eq := hVK.symm
      N_eq := rfl
      P_le_N := hPN
      card_P := hcardP
      R_le_normalizer_P := hRP
      U_subgroupOf_eq := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      inf_K_V := by rw [inf_comm]; exact hVKbot
      coprime_card_K := hcopK
      sup_V_N := hVN
      commutator_K_P_ne_bot := hKP }
  have hker : IsPrimeCentralizerKernelSetup p H R R0 V K U N P :=
    { admissible := hadm
      prime_p := Fact.out
      not_hasPLengthLeOne := hnot
      minimal := hmin
      V_eq := rfl
      K_le_H := hcompl.K_le_H
      R_le_normalizer_K := hRK
      U_eq := hVK.symm
      N_eq := rfl
      P_le_N := hPN
      card_P := hcardP
      R_le_normalizer_P := hRP
      U_subgroupOf_eq := hcompl.U_subgroupOf_eq
      inf_K_V := hcompl.inf_K_V
      coprime_card_K := hcopK
      sup_V_N := hVN
      commutator_K_P_ne_bot := hKP
      inf_V_centralizer_K := hcompl.inf_centralizer_eq_bot
      inf_V_N := hcompl.inf_N_eq_bot
      K_eq_fittingRaw_N := hcompl.K_eq_map_subtype_fittingRaw_N
      inf_H_centralizer_K_le := hcompl.inf_centralizer_le }
  obtain ⟨q, hred⟩ := hker.isReducedPrimeCentralizerKernel
  obtain ⟨d, hd, -⟩ := hred.exists_natCard_eq_pow_mulEquiv_pi
  exact not_isTransitiveHyperplaneSetup (p := p) (q := q) (d := d)
    (H := H) (R := R) (R0 := R0) (V := V) (K := K) (U := U) (N := N) (P := P)
    { reduced := hred
      isElementaryAbelian_K := hred.isElementaryAbelian_K
      card_K := hd
      three_le := hred.three_le_of_natCard_eq_pow hd
      card_inf_centralizer_R := by rw [hred.R_eq]; exact hker.natCard_inf_V_centralizer_R0
      relIndex_commutator := hred.index_commutator_K_R }

private theorem hasPLengthLeOne_commutator_aux :
    ∀ (n : ℕ) (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
      Nat.card Y < n → IsAdmissibleCoprimeActionQuadruple Y J A A0 →
      HasPLengthLeOne p ↥⁅J, A⁆ := by
  intro n
  induction n with
  | zero => intro Y _ _ J A A0 hlt; omega
  | succ n ih =>
    intro Y _ _ J A A0 hlt hadm
    by_contra hnot
    exact false_of_not_hasPLengthLeOne_of_minimal hadm hnot
      fun Z _ _ J' A' A0' hZ hcard => ih Z J' A' A0' (by omega) hZ

theorem hasPLengthLeOne_commutator_of_admissible
    (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0) : HasPLengthLeOne p ↥⁅H, R⁆ :=
  hasPLengthLeOne_commutator_aux (Nat.card G + 1) G H R R0 (Nat.lt_succ_self _) hadm

theorem primeCentralizerCommutatorPrimeLength {X : Type u} [Group X] [Finite X]
    {H R R0 : Subgroup X} (hadm : IsAdmissibleCoprimeActionQuadruple X H R R0) :
    ∀ p : ℕ, p.Prime → HasPLengthLeOne p ↥⁅H, R⁆ := fun p hp =>
  have := Fact.mk hp
  hasPLengthLeOne_commutator_of_admissible (p := p) hadm

theorem primeCentralizerCommutatorPrimeLength_of_coe_mul_coe {X : Type u} [Group X] [Finite X]
    {H R R0 : Subgroup X} (hsolv : Group.IsSolvable X) (hodd : Odd (Nat.card X)) (hHn : H.Normal)
    (hprod : (H : Set X) * (R : Set X) = Set.univ) (hinf : H ⊓ R = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card R)) (hR0 : R0 ≤ R) (hR0card : (Nat.card R0).Prime)
    (hZ : ∀ t : ℕ, t.Prime →
      ∀ Q : Sylow t (centralizer (R0 : Set X) ⊓ H : Subgroup X), IsCyclic Q) :
    ∀ p : ℕ, p.Prime → HasPLengthLeOne p ↥⁅H, R⁆ :=
  primeCentralizerCommutatorPrimeLength (isAdmissibleCoprimeActionQuadruple_of_coe_mul_coe hsolv
    hodd hHn hprod hinf hcop hR0 hR0card hZ)

end

end CFSG.FeitThompson
