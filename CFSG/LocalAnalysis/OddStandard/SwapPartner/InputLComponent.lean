module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLAbar
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

private theorem alternatingGroup_fin_eight_nonabelian :
    ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin 8)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h8 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 8)).mp this
  simp at h8

theorem isQuasisimple_center_eq_bot_of_alt8 {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 8)) : CFSG.IsQuasisimple G ∧ center G = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup G := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := alternatingGroup_fin_eight_nonabelian
  refine CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨e.symm a, e.symm b, ?_⟩
  intro h
  exact hab (by simpa using congrArg e h)

theorem nonempty_quotient_center_equiv_alt8 {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 8)) :
    Nonempty (G ⧸ center G ≃* alternatingGroup (Fin 8)) := by
  have hZ : center G = ⊥ := (isQuasisimple_center_eq_bot_of_alt8 e).2
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

@[expose] noncomputable def fixedAbar (t : X) (Sg K : Subgroup X) [K.Normal] :
    Subgroup ↥(fixedSubgroup (quotConj K t)) :=
  (quotAbar Sg K).subgroupOf (fixedSubgroup (quotConj K t))

theorem SwapShape.orderOf_quotConj_eq_two [K.Normal] (h : SwapShape t Sg V) (hK : ⁅K, K⁆ = K)
    (hne : ⁅Sg, Sg⁆ ≠ K) (hA : ⁅Sg, Sg⁆ ≤ K) : orderOf (quotConj K t) = 2 := by
  have ht : t * t = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.order_eq])
  apply orderOf_eq_prime
  · rw [sq]
    exact quotConj_mul_self ht
  · exact SwapShape.quotConj_ne_one h hK hne hA

theorem SwapShape.quotAbar_le_fixedSubgroup [K.Normal] (h : SwapShape t Sg V)
    (hA : ⁅Sg, Sg⁆ ≤ K) : quotAbar Sg K ≤ fixedSubgroup (quotConj K t) := by
  unfold quotAbar
  exact map_le_fixedSubgroup_quotConj hA h.commutator_sg_le_centralizer

theorem SwapShape.fixedAbar_equiv [K.Normal] (h : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) :
    Nonempty (↥(fixedAbar t Sg K) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := h.quotAbar_equiv hA
  unfold fixedAbar
  exact ⟨(Subgroup.subgroupOfEquivOfLe (h.quotAbar_le_fixedSubgroup hA)).trans e⟩

theorem SwapShape.isSubnormal_fixedAbar [K.Normal] (h : SwapShape t Sg V)
    (hA : ⁅Sg, Sg⁆ ≤ K) : (fixedAbar t Sg K).IsSubnormal := by
  unfold fixedAbar quotAbar
  exact isSubnormal_map_subgroupOf_fixedSubgroup hA h.commutator_sg_le_centralizer
    (inf_le_right.trans h.centralizer_le_normalizer_commutator)

theorem SwapShape.isComponent_fixedAbar [K.Normal] (h : SwapShape t Sg V)
    (hA : ⁅Sg, Sg⁆ ≤ K) : CFSG.IsComponent (fixedAbar t Sg K) := by
  obtain ⟨e⟩ := h.fixedAbar_equiv hA
  exact ⟨(isQuasisimple_center_eq_bot_of_alt8 e).1, h.isSubnormal_fixedAbar hA⟩

theorem SwapShape.fixedAbar_quotCenter_equiv [K.Normal] (h : SwapShape t Sg V)
    (hA : ⁅Sg, Sg⁆ ≤ K) :
    Nonempty (↥(fixedAbar t Sg K) ⧸ center ↥(fixedAbar t Sg K) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := h.fixedAbar_equiv hA
  exact nonempty_quotient_center_equiv_alt8 e

theorem SwapShape.card_center_fixedAbar [K.Normal] (h : SwapShape t Sg V)
    (hA : ⁅Sg, Sg⁆ ≤ K) : Nat.card (center ↥(fixedAbar t Sg K)) = 1 := by
  obtain ⟨e⟩ := h.fixedAbar_equiv hA
  rw [(isQuasisimple_center_eq_bot_of_alt8 e).2, Subgroup.card_bot]

end CFSG.OddStandard.AltStdSec.SwapPartner
