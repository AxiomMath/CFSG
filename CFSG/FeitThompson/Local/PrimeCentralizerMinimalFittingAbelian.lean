module

public import Mathlib.GroupTheory.Frattini
public import CFSG.FeitThompson.Definitions.AdmissibleCoprimeActionQuadruple
public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PLengthOneQuotientLift
import CFSG.FeitThompson.Local.SelfCentralizingFrattiniPrimeCore
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement

universe u

section Aux

variable {p : ℕ} {Y : Type*} [Group Y]

theorem centralizer_map_subtype_inf {H : Subgroup Y} (K : Subgroup ↥H) :
    Subgroup.centralizer ((K.map H.subtype : Subgroup Y) : Set Y) ⊓ H
      = (Subgroup.centralizer (K : Set ↥H)).map H.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
    Subgroup.coe_subtype, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hxH⟩
    exact ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.2 fun k hk =>
      Subtype.ext (hx (k : Y) ⟨k, hk, rfl⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rintro g ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy k hk)

theorem IsElementaryAbelian.map_subtype {H : Subgroup Y} {K : Subgroup ↥H}
    (h : IsElementaryAbelian p K) : IsElementaryAbelian p (K.map H.subtype) := by
  refine isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_, ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby]
    exact congrArg Subtype.val (h.mul_comm ha hb)
  · rintro x ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (h.pow_eq_one ha)

variable [Finite Y]

theorem exists_normal_isPGroup_not_dvd_index_of_pComplCore_eq_bot [Fact p.Prime]
    (hcore : pComplCore p Y = ⊥) (h : HasPLengthLeOne p Y) :
    ∃ T : Subgroup Y, T.Normal ∧ IsPGroup p T ∧ ¬ p ∣ T.index := by
  rw [hasPLengthLeOne_iff_exists_normal] at h
  obtain ⟨D, T, hD, hT, hDT, hDcard, ⟨n, hn⟩, hTidx⟩ := h
  have hDbot : D = ⊥ := le_bot_iff.1 (hcore ▸
    le_pComplCore hD fun hmem => hDcard (Nat.dvd_of_mem_primeFactors hmem))
  refine ⟨T, hT, IsPGroup.of_card (n := n) ?_, hTidx⟩
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf T)
  rw [hn, hDbot, Subgroup.bot_subgroupOf, Subgroup.card_bot, mul_one] at hc
  exact hc

theorem hasPLengthLeOne_of_isPGroup_of_not_dvd_index [Fact p.Prime] {T : Subgroup Y}
    (hTn : T.Normal) (hT : IsPGroup p T) (hidx : ¬ p ∣ T.index) : HasPLengthLeOne p Y := by
  rw [hasPLengthLeOne_iff_exists_normal]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT
  refine ⟨⊥, T, inferInstance, hTn, bot_le, ?_, ⟨n, ?_⟩, hidx⟩
  · rw [Subgroup.card_bot, Nat.dvd_one]
    exact (Fact.out : p.Prime).one_lt.ne'
  · rw [natCard_quotient_subgroupOf, Subgroup.relIndex_bot_left, hn]

theorem hasPLengthLeOne_of_quotient_of_pComplCore_eq_bot [Fact p.Prime] {F : Subgroup Y}
    [F.Normal] (hF : IsPGroup p F) (hcore : pComplCore p (Y ⧸ F) = ⊥)
    (h : HasPLengthLeOne p (Y ⧸ F)) : HasPLengthLeOne p Y := by
  obtain ⟨S, hSn, hS, hSidx⟩ := exists_normal_isPGroup_not_dvd_index_of_pComplCore_eq_bot hcore h
  set T : Subgroup Y := S.comap (QuotientGroup.mk' F) with hTdef
  have hFT : F ≤ T := by
    intro x hx
    simp only [hTdef, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hF
  refine hasPLengthLeOne_of_isPGroup_of_not_dvd_index (T := T) (hSn.comap _)
    (IsPGroup.of_card (n := a + b) ?_) ?_
  · have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.subgroupOf T)
    rw [natCard_quotient_subgroupOf, hTdef, relIndex_comap_mk' F S,
      natCard_subgroupOf_of_le hFT, ha, hb, ← pow_add] at hc
    exact hc
  · rw [hTdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective F)]
    exact hSidx

theorem hasPLengthLeOne_of_quotient_map_subtype_frattini [Fact p.Prime] {V : Subgroup Y}
    [V.Normal] (hV : IsPGroup p V) (hC : Subgroup.centralizer (V : Set Y) ≤ V)
    (h : HasPLengthLeOne p (Y ⧸ (frattini ↥V).map V.subtype)) : HasPLengthLeOne p Y :=
  hasPLengthLeOne_of_quotient_of_pComplCore_eq_bot
    ((hV.to_subgroup (frattini ↥V)).map V.subtype)
    (pComplCore_quotient_map_subtype_frattini_eq_bot Fact.out hV hC) h

theorem isElementaryAbelian_of_frattini_eq_bot [Fact p.Prime] {V : Subgroup Y}
    (hV : IsPGroup p V) (h : frattini ↥V = ⊥) : IsElementaryAbelian p V := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hV
  refine isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => ?_⟩
  · have hxy : ⁅x, y⁆ ∈ _root_.commutator ↥V :=
      Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
    have h2 := ((commutator_le_frattini (n := n) Fact.out hn).trans h.le) hxy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  · have h2 := h.le (pow_mem_frattini (n := n) Fact.out hn (⟨x, hx⟩ : ↥V))
    rw [Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2

end Aux

section Main

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H R R0 : Subgroup G}
  (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
  (hnot : ¬ HasPLengthLeOne p ↥⁅H, R⁆)
  (hmin : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
    HasPLengthLeOne p ↥⁅J, A⁆)

include hadm hnot hmin

theorem fittingRaw_eq_pCore_of_minimal : fittingRaw ↥H = pCore p ↥H :=
  have : Group.IsSolvable G := hadm.isSolvable
  fittingRaw_eq_pCore_of_pComplCore_eq_bot Fact.out (pComplCore_eq_bot_of_minimal hadm hnot hmin)

theorem fittingRaw_ne_bot_of_minimal : fittingRaw ↥H ≠ ⊥ := by
  have : Group.IsSolvable G := hadm.isSolvable
  have hne : Nontrivial ↥H :=
    (Subgroup.nontrivial_iff_ne_bot H).2 (ne_bot_of_minimal hadm hnot hmin)
  rw [fittingRaw_eq_pCore_of_minimal hadm hnot hmin]
  exact pCore_ne_bot_of_pComplCore_eq_bot Fact.out (pComplCore_eq_bot_of_minimal hadm hnot hmin)

theorem isPGroup_fittingRaw_of_minimal : IsPGroup p ↥(fittingRaw ↥H) := by
  rw [fittingRaw_eq_pCore_of_minimal hadm hnot hmin]
  exact isPGroup_pCore Fact.out _

theorem centralizer_fittingRaw_le_of_minimal :
    Subgroup.centralizer ((fittingRaw ↥H : Subgroup ↥H) : Set ↥H) ≤ fittingRaw ↥H := by
  have : Group.IsSolvable G := hadm.isSolvable
  rw [fittingRaw_eq_pCore_of_minimal hadm hnot hmin]
  exact centralizer_pCore_le_pCore Fact.out (pComplCore_eq_bot_of_minimal hadm hnot hmin)

theorem frattini_fittingRaw_eq_bot_of_minimal : frattini ↥(fittingRaw ↥H : Subgroup ↥H) = ⊥ := by
  have hHn := hadm.normal
  set U : Subgroup ↥H := fittingRaw ↥H with hU
  have hUp : IsPGroup p ↥U := isPGroup_fittingRaw_of_minimal hadm hnot hmin
  have hUC := centralizer_fittingRaw_le_of_minimal hadm hnot hmin
  by_contra hne
  set D : Subgroup G := ((frattini ↥U).map U.subtype).map H.subtype with hD
  have _i1 : ((frattini ↥U).map U.subtype).Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  have _i2 : D.Normal := ConjAct.normal_of_characteristic_of_normal
  have hDne : D ≠ ⊥ := by
    rw [hD, Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective]
    exact hne
  have heq : D.subgroupOf H = (frattini ↥U).map U.subtype :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have _i3 : ((frattini ↥U).map U.subtype).Normal := Subgroup.normal_of_characteristic _
  have _i4 : (D.subgroupOf H).Normal := heq ▸ _i3
  have hq := hasPLengthLeOne_quotient_of_minimal hadm hnot hmin hDne (Subgroup.map_subtype_le _)
  have hq' : HasPLengthLeOne p (↥H ⧸ (frattini ↥U).map U.subtype) :=
    hq.of_surjective (f := ((QuotientGroup.quotientMulEquivOfEq heq) :
        (↥H ⧸ D.subgroupOf H) →* ↥H ⧸ (frattini ↥U).map U.subtype))
      (QuotientGroup.quotientMulEquivOfEq heq).surjective
  exact not_hasPLengthLeOne_of_minimal hadm hnot hmin
    (hasPLengthLeOne_of_quotient_map_subtype_frattini hUp hUC hq')

theorem isElementaryAbelian_fittingRaw_of_minimal :
    IsElementaryAbelian p (fittingRaw ↥H : Subgroup ↥H) :=
  isElementaryAbelian_of_frattini_eq_bot (isPGroup_fittingRaw_of_minimal hadm hnot hmin)
    (frattini_fittingRaw_eq_bot_of_minimal hadm hnot hmin)

theorem centralizer_fittingRaw_eq_of_minimal :
    Subgroup.centralizer ((fittingRaw ↥H : Subgroup ↥H) : Set ↥H) = fittingRaw ↥H :=
  le_antisymm (centralizer_fittingRaw_le_of_minimal hadm hnot hmin)
    (Subgroup.le_centralizer_iff_isMulCommutative.2
      (isElementaryAbelian_fittingRaw_of_minimal hadm hnot hmin).isMulCommutative)

theorem isElementaryAbelian_map_subtype_fittingRaw_of_minimal :
    IsElementaryAbelian p ((fittingRaw ↥H).map H.subtype) :=
  (isElementaryAbelian_fittingRaw_of_minimal hadm hnot hmin).map_subtype

theorem centralizer_map_subtype_fittingRaw_inf_eq_of_minimal :
    Subgroup.centralizer (((fittingRaw ↥H).map H.subtype : Subgroup G) : Set G) ⊓ H
      = (fittingRaw ↥H).map H.subtype := by
  rw [centralizer_map_subtype_inf, centralizer_fittingRaw_eq_of_minimal hadm hnot hmin]

theorem exists_mulEquiv_pi_fittingRaw_of_minimal :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥(fittingRaw ↥H) = p ^ d ∧
      Nonempty (↥(fittingRaw ↥H) ≃* (Fin d → Multiplicative (ZMod p))) := by
  have hea := isElementaryAbelian_fittingRaw_of_minimal hadm hnot hmin
  obtain ⟨d, hd⟩ := hea.exists_natCard_eq_pow (p := p) Fact.out
  refine ⟨d, ?_, hd, nonempty_mulEquiv_pi_of_isElementaryAbelian Fact.out hea hd⟩
  rcases Nat.eq_zero_or_pos d with rfl | h
  · rw [pow_zero, Subgroup.card_eq_one] at hd
    exact absurd hd (fittingRaw_ne_bot_of_minimal hadm hnot hmin)
  · exact h

theorem fittingRaw_minimalPrimeCentralizerCounterexample :
    fittingRaw ↥H = pCore p ↥H ∧ fittingRaw ↥H ≠ ⊥ ∧
      ((fittingRaw ↥H).map H.subtype).Normal ∧
      Subgroup.centralizer ((fittingRaw ↥H : Subgroup ↥H) : Set ↥H) = fittingRaw ↥H ∧
      ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥(fittingRaw ↥H) = p ^ d ∧
        Nonempty (↥(fittingRaw ↥H) ≃* (Fin d → Multiplicative (ZMod p))) :=
  ⟨fittingRaw_eq_pCore_of_minimal hadm hnot hmin, fittingRaw_ne_bot_of_minimal hadm hnot hmin,
    normal_map_subtype_fittingRaw hadm.normal, centralizer_fittingRaw_eq_of_minimal hadm hnot hmin,
    exists_mulEquiv_pi_fittingRaw_of_minimal hadm hnot hmin⟩

end Main

end

end CFSG.FeitThompson
