module

public import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.PrimeSubgroupFixesFittingLine
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.PLengthOneQuotientLift
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
import CFSG.FeitThompson.Local.SylowNormalizerNotCentralizing
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.OddOrder.SemidirectReassociation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] {p : ℕ}

section Aux

variable [Finite G]

private theorem pComplCore_eq_bot_of_selfCentralizing (hp : p.Prime) {H0 V : Subgroup G}
    (hVn : V.Normal) (hVH0 : V ≤ H0) (hVp : IsPGroup p ↥V)
    (hself : ∀ w ∈ H0, (∀ v ∈ V, v * w = w * v) → w ∈ V) : pComplCore p ↥H0 = ⊥ := by
  have := Fact.mk hp
  have := hVn
  set W : Subgroup ↥H0 := pComplCore p ↥H0 with hW
  have hWn : W.Normal := pComplCore_normal p ↥H0
  have hVn' : (V.subgroupOf H0).Normal := hVn.subgroupOf H0
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hVp
  have hV'p : IsPGroup p ↥(V.subgroupOf H0) :=
    IsPGroup.of_card (by rw [natCard_subgroupOf_of_le hVH0, hn])
  have hcop : p.Coprime (Nat.card ↥W) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_natCard_pComplCore hp _)
  have hinf : V.subgroupOf H0 ⊓ W = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hp hV'p hcop
  have hle : W ≤ centralizer ((V.subgroupOf H0 : Subgroup ↥H0) : Set ↥H0) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (le_bot_iff.1 ((Subgroup.commutator_le_inf W _).trans (by rw [inf_comm]; exact hinf.le)))
  have hmap : W.map H0.subtype ≤ V := by
    rintro x ⟨w, hw, rfl⟩
    exact hself _ w.2 fun v hv => congrArg Subtype.val
      ((mem_centralizer_iff.1 (hle hw)) ⟨v, hVH0 hv⟩ (Subgroup.mem_subgroupOf.2 hv))
  have hcardeq : Nat.card ↥W = Nat.card ↥(W.map H0.subtype) :=
    Nat.card_congr (Subgroup.equivMapOfInjective W H0.subtype H0.subtype_injective).toEquiv
  exact Subgroup.card_eq_one.1 ((hcop.symm.pow_right n).eq_one_of_dvd
    (hn ▸ (hcardeq ▸ Subgroup.card_dvd_of_le hmap)))

private theorem pComplCore_eq_bot_of_le_normalizer (hp : p.Prime) {H0 D : Subgroup G}
    (hDH0 : D ≤ H0) (hnorm : H0 ≤ normalizer (D : Set G)) (h : pComplCore p ↥H0 = ⊥) :
    pComplCore p ↥D = ⊥ := by
  have hchar : (pComplCore p ↥D).Characteristic := by
    rw [pComplCore_eq_piCore]; infer_instance
  have hWH0 : (pComplCore p ↥D).map D.subtype ≤ H0 := (Subgroup.map_subtype_le _).trans hDH0
  have hWn : (((pComplCore p ↥D).map D.subtype).subgroupOf H0).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_map_subtype_of_characteristic _ hnorm)
  have hcard : Nat.card ↥(((pComplCore p ↥D).map D.subtype).subgroupOf H0)
      = Nat.card ↥(pComplCore p ↥D) := by
    rw [natCard_subgroupOf_of_le hWH0]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).toEquiv).symm
  have hple : ((pComplCore p ↥D).map D.subtype).subgroupOf H0 ≤ pComplCore p ↥H0 := by
    refine le_pComplCore hWn ?_
    rw [hcard]
    exact fun hmem => not_dvd_natCard_pComplCore hp _ (Nat.dvd_of_mem_primeFactors hmem)
  rw [h, le_bot_iff] at hple
  refine (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 ?_
  rw [← Subgroup.map_subgroupOf_eq_of_le hWH0, hple, Subgroup.map_bot]

private theorem le_map_pCore_of_hasPLengthLeOne (hp : p.Prime) {D Q : Subgroup G}
    (hcore : pComplCore p ↥D = ⊥) (hlen : HasPLengthLeOne p ↥D) (hQD : Q ≤ D)
    (hQp : IsPGroup p ↥Q) : Q ≤ (pCore p ↥D).map D.subtype := by
  have := Fact.mk hp
  obtain ⟨T, hTn, hTp, hTidx⟩ :=
    exists_normal_isPGroup_not_dvd_index_of_pComplCore_eq_bot hcore hlen
  set S : Subgroup ↥D := pCore p ↥D with hS
  have hSn : S.Normal := pCore_normal p ↥D
  have hSp : IsPGroup p ↥S := isPGroup_pCore hp ↥D
  have hSidx : ¬ p ∣ S.index := fun hd =>
    hTidx (hd.trans (Subgroup.index_dvd_of_le (le_pCore hp hTn hTp)))
  have huniq : Unique (Sylow p ↥D) :=
    (hSp.toSylow hSidx).unique_of_normal (by rw [IsPGroup.toSylow_coe]; exact hSn)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
  obtain ⟨Q', hQ'⟩ := (IsPGroup.of_card (n := n)
    (by rw [natCard_subgroupOf_of_le hQD, hn]) : IsPGroup p ↥(Q.subgroupOf D)).exists_le_sylow
  have hQ'eq : (Q' : Subgroup ↥D) = S := by
    rw [Subsingleton.elim Q' (hSp.toSylow hSidx), IsPGroup.toSylow_coe]
  calc Q = (Q.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hQD).symm
    _ ≤ S.map D.subtype := Subgroup.map_mono (hQ'eq ▸ hQ')

end Aux

theorem isAdmissible_subgroupOf_sup_self {H R R0 : Subgroup G}
    (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0) {B : Subgroup G} (hBH : B ≤ H)
    (hnorm : R0 ≤ normalizer (B : Set G)) :
    IsAdmissibleCoprimeActionQuadruple ↥(B ⊔ R0) (B.subgroupOf (B ⊔ R0))
      (R0.subgroupOf (B ⊔ R0)) (R0.subgroupOf (B ⊔ R0)) := by
  have hsolv : Group.IsSolvable G := hadm.isSolvable
  have hZ := hadm.isZGroup_centralizer
  set L : Subgroup G := B ⊔ R0 with hLdef
  have hBL : B ≤ L := le_sup_left
  have hR0L : R0 ≤ L := le_sup_right
  refine ⟨inferInstance, hadm.odd_card_subgroup L, normal_subgroupOf_sup hnorm, ?_, ?_, ?_,
    le_rfl, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hBL hR0L, ← hLdef, subgroupOf_self]
  · rw [← subgroupOf_inf, show B ⊓ R0 = ⊥ from le_bot_iff.1
      ((inf_le_inf hBH hadm.le).trans hadm.inf_eq_bot.le), Subgroup.bot_subgroupOf]
  · rw [natCard_subgroupOf_of_le hBL, natCard_subgroupOf_of_le hR0L]
    exact (hadm.coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hBH)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hadm.le)
  · rw [natCard_subgroupOf_of_le hR0L]; exact hadm.prime_card
  · refine isZGroup_of_map_subtype_le (W := centralizer (R0 : Set G) ⊓ H) _ ?_
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val ((mem_centralizer_iff.1 hy1) (⟨g, hR0L hg⟩ : ↥L)
        (by simpa [Subgroup.mem_subgroupOf] using hg)),
      hBH (Subgroup.mem_subgroupOf.1 hy2)⟩

variable [Finite G] {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerKernelSetup p H R R0 V K U N P)

namespace IsPrimeCentralizerKernelSetup

include hc

variable {X : Subgroup G}

theorem sup_V_X_P_le_H (hX : X ≤ K) : V ⊔ X ⊔ P ≤ H :=
  sup_le (sup_le hc.V_le_H (le_trans hX hc.K_le_H)) (hc.P_le_N.trans hc.N_le_H)

theorem R0_le_normalizer_sup (hXR0 : R0 ≤ normalizer (X : Set G)) :
    R0 ≤ normalizer ((V ⊔ X ⊔ P : Subgroup G) : Set G) :=
  have := hc.normal_V
  fun _ hg => mem_normalizer_sup
    (mem_normalizer_sup (Subgroup.le_normalizer_of_normal hg) (hXR0 hg))
    ((hc.admissible.le.trans hc.R_le_normalizer_P) hg)

theorem coe_sup_V_X_P_R0 (hXP : P ≤ normalizer (X : Set G))
    (hXR0 : R0 ≤ normalizer (X : Set G)) :
    ((V ⊔ X ⊔ P ⊔ R0 : Subgroup G) : Set G)
      = (V : Set G) * (X : Set G) * (P : Set G) * (R0 : Set G) := by
  have := hc.normal_V
  have hP : P ≤ normalizer ((V ⊔ X : Subgroup G) : Set G) := fun _ hg =>
    mem_normalizer_sup (Subgroup.le_normalizer_of_normal hg) (hXP hg)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hc.R0_le_normalizer_sup hXR0),
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hP, Subgroup.normal_mul]

theorem commutator_X_P_eq_bot (hX : X ≤ K) (hXP : P ≤ normalizer (X : Set G))
    (hXR0 : R0 ≤ normalizer (X : Set G)) (hproper : V ⊔ X ⊔ P ⊔ R0 ≠ ⊤) :
    (⁅X, P⁆ : Subgroup G) = ⊥ := by
  have := Fact.mk hc.prime_p
  have hVn := hc.normal_V
  set H0 : Subgroup G := V ⊔ X ⊔ P with hH0
  set L : Subgroup G := H0 ⊔ R0 with hL
  have hH0H : H0 ≤ H := hc.sup_V_X_P_le_H hX
  have hR0norm : R0 ≤ normalizer (H0 : Set G) := hc.R0_le_normalizer_sup hXR0
  have hH0L : H0 ≤ L := le_sup_left
  have hR0L : R0 ≤ L := le_sup_right
  have hadm' := isAdmissible_subgroupOf_sup_self hc.admissible hH0H hR0norm
  have hplen := hc.minimal ↥L _ _ _ hadm' (natCard_lt_natCard_of_ne_top hproper)
  set D : Subgroup G := ⁅H0, R0⁆ with hD
  have hDH0 : D ≤ H0 :=
    (Subgroup.commutator_mono le_rfl hR0norm).trans (commutator_normalizer_le H0)
  have hDL : D ≤ L := hDH0.trans hH0L
  rw [commutator_subgroupOf hH0L hR0L] at hplen
  have hlenD : HasPLengthLeOne p ↥D :=
    hplen.of_surjective (f := ((Subgroup.subgroupOfEquivOfLe hDL) : ↥(D.subgroupOf L) →* ↥D))
      (Subgroup.subgroupOfEquivOfLe hDL).surjective
  have hVH0 : V ≤ H0 := le_sup_left.trans le_sup_left
  have hcoreH0 : pComplCore p ↥H0 = ⊥ :=
    pComplCore_eq_bot_of_selfCentralizing hc.prime_p hVn hVH0
      hc.isElementaryAbelian_V.isPGroup fun w hw hcomm =>
        hc.centralizer_V_inf_H ▸ ⟨mem_centralizer_iff.2 hcomm, hH0H hw⟩
  have hH0normD : H0 ≤ normalizer (D : Set G) := Subgroup.normalizer_commutator_ge_left H0 R0
  have hcoreD : pComplCore p ↥D = ⊥ :=
    pComplCore_eq_bot_of_le_normalizer hc.prime_p hDH0 hH0normD hcoreH0
  have hPD : P ≤ D := by
    rw [← hc.commutator_P_R0_eq]
    exact Subgroup.commutator_mono (le_sup_right : P ≤ H0) le_rfl
  have hPW : P ≤ (pCore p ↥D).map D.subtype :=
    le_map_pCore_of_hasPLengthLeOne hc.prime_p hcoreD hlenD hPD hc.isPGroup_P
  have hWchar : (pCore p ↥D).Characteristic := by rw [pCore_eq_piCore]; infer_instance
  have hH0normW : H0 ≤ normalizer (((pCore p ↥D).map D.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_characteristic _ hH0normD
  have hXH0 : X ≤ H0 := le_sup_right.trans le_sup_left
  have hXPW : (⁅X, P⁆ : Subgroup G) ≤ (pCore p ↥D).map D.subtype := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hPW (hXH0.trans hH0normW)).trans (commutator_normalizer_le _)
  have hXPX : (⁅X, P⁆ : Subgroup G) ≤ X :=
    (Subgroup.commutator_mono le_rfl hXP).trans (commutator_normalizer_le X)
  exact le_bot_iff.1 ((le_inf hXPW hXPX).trans
    (inf_eq_bot_of_isPGroup_of_coprime hc.prime_p ((isPGroup_pCore hc.prime_p ↥D).map _)
      (hc.coprime_card_K.symm.coprime_dvd_right (Subgroup.card_dvd_of_le hX))).le)

theorem le_centralizer_P_of_proper (hX : X ≤ K) (hXP : P ≤ normalizer (X : Set G))
    (hXR0 : R0 ≤ normalizer (X : Set G)) (hproper : V ⊔ X ⊔ P ⊔ R0 ≠ ⊤) :
    X ≤ centralizer (P : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hc.commutator_X_P_eq_bot hX hXP hXR0 hproper)

end IsPrimeCentralizerKernelSetup

end CFSG.FeitThompson

end
