module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute
import CFSG.FeitThompson.OddOrder.NoncentralComplementHallCore
import CFSG.FeitThompson.OddOrder.OuterFactorFreeOnInnerComplement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {M : Type*} [Group M]

theorem natCard_subgroupOf {K L : Subgroup M} (h : K ≤ L) :
    Nat.card (K.subgroupOf L) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_zpowers_eq_of_prime_natCard {B : Subgroup M} (hB : (Nat.card B).Prime) :
    ∃ b ∈ B, b ≠ 1 ∧ Subgroup.zpowers b = B := by
  have hfact := Fact.mk hB
  have hBne : B ≠ ⊥ := fun h => hB.ne_one (by rw [h, Subgroup.card_bot])
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  refine ⟨(a : M), a.2, by simpa using ha, le_antisymm (Subgroup.zpowers_le.mpr a.2) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card (p := Nat.card B) rfl ha (g' := ⟨x, hx⟩))
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg (Subgroup.subtype B) hn⟩

theorem centralizer_coe_eq_centralizer_singleton {B : Subgroup M} {b : M}
    (hb : Subgroup.zpowers b = B) : centralizer (B : Set M) = centralizer {b} := by
  rw [← hb, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

structure IsPTypeConfig (H J U B F W2 : Subgroup M) : Prop where
  finite : Finite M
  isSolvable : Group.IsSolvable M
  eq_commutator : J = commutator M
  normal_H : H.Normal
  isNilpotent_H : Group.IsNilpotent H
  hall_H : (Nat.card H).Coprime H.index
  max_H : ∀ K : Subgroup M, Group.IsNilpotent K → K.Normal →
    (Nat.card K).Coprime K.index → K ≤ H
  normal_F : F.Normal
  isNilpotent_F : Group.IsNilpotent F
  max_F : ∀ K : Subgroup M, Group.IsNilpotent K → K.Normal → K ≤ F
  isComplement'_J_B : J.IsComplement' B
  sup_eq_J : H ⊔ U = J
  disjoint_H_U : Disjoint H U
  ne_bot_U : U ≠ ⊥
  isNilpotent_U : Group.IsNilpotent U
  prime_natCard_B : (Nat.card B).Prime
  hall_B : (Nat.card B).Coprime B.index
  le_normalizer_U : B ≤ normalizer (U : Set M)
  ne_bot_H : H ≠ ⊥
  commutator_J_le_F : ⁅J, J⁆ ≤ F
  isCyclic_W2 : IsCyclic W2
  ne_bot_W2 : W2 ≠ ⊥
  le_H_W2 : W2 ≤ H
  inf_centralizer_eq_W2 : ∀ b ∈ B, b ≠ 1 → J ⊓ centralizer {b} = W2

namespace IsPTypeConfig

variable {H J U B F W2 : Subgroup M} (hc : IsPTypeConfig H J U B F W2)

include hc

theorem normal_J : J.Normal := hc.eq_commutator ▸ (inferInstance : (commutator M).Normal)

theorem le_J_H : H ≤ J := hc.sup_eq_J ▸ le_sup_left

theorem le_J_U : U ≤ J := hc.sup_eq_J ▸ le_sup_right

theorem isCyclic_B : IsCyclic B :=
  have := Fact.mk hc.prime_natCard_B
  isCyclic_of_prime_card (p := Nat.card B) rfl

theorem coe_sup_eq_coe_mul_coe : ((U ⊔ B : Subgroup M) : Set M) = (U : Set M) * (B : Set M) :=
  Subgroup.coe_mul_of_right_le_normalizer_left U B hc.le_normalizer_U

theorem isComplement'_H_sup : H.IsComplement' (U ⊔ B) :=
  have := hc.normal_H
  isComplement'_sup hc.isComplement'_J_B hc.sup_eq_J hc.disjoint_H_U hc.le_normalizer_U

theorem disjoint_U_B : Disjoint U B :=
  disjoint_of_isComplement'_of_sup_eq hc.isComplement'_J_B hc.sup_eq_J

theorem normal_subgroupOf_U_sup : (U.subgroupOf (U ⊔ B)).Normal :=
  normal_subgroupOf_sup hc.le_normalizer_U

theorem isComplement'_subgroupOf_U_sup :
    (U.subgroupOf (U ⊔ B)).IsComplement' (B.subgroupOf (U ⊔ B)) :=
  isComplement'_subgroupOf_sup hc.le_normalizer_U hc.disjoint_U_B

theorem coprime_natCard_H_sup : (Nat.card H).Coprime (Nat.card (U ⊔ B : Subgroup M)) :=
  have := hc.normal_H
  coprime_natCard_sup hc.isComplement'_J_B hc.sup_eq_J hc.disjoint_H_U hc.le_normalizer_U hc.hall_H

theorem natCard_sup : Nat.card (U ⊔ B : Subgroup M) = Nat.card U * Nat.card B :=
  natCard_sup_of_le_normalizer hc.le_normalizer_U hc.disjoint_U_B

theorem inf_centralizer_U_eq_bot : ∀ b ∈ B, b ≠ 1 → U ⊓ centralizer {b} = ⊥ :=
  have := hc.normal_J
  have := hc.normal_H.subgroupOf J
  inf_centralizer_eq_bot_of_inf_centralizer_le hc.isComplement'_J_B hc.sup_eq_J hc.disjoint_H_U
    hc.le_normalizer_U fun b hb hb1 => (hc.inf_centralizer_eq_W2 b hb hb1).le.trans hc.le_H_W2

theorem not_commute_of_mem_U {b x : M} (hb : b ∈ B) (hb1 : b ≠ 1) (hx : x ∈ U) (hx1 : x ≠ 1) :
    ¬ Commute x b := by
  intro hcomm
  refine hx1 (Subgroup.mem_bot.mp ?_)
  rw [← hc.inf_centralizer_U_eq_bot b hb hb1]
  exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩

theorem inf_centralizer_B_eq_W2 : H ⊓ centralizer (B : Set M) = W2 := by
  obtain ⟨b, hbB, hb1, hbgen⟩ := exists_zpowers_eq_of_prime_natCard hc.prime_natCard_B
  have h1 : H ⊓ centralizer {b} = H ⊓ (J ⊓ centralizer {b}) := by
    rw [← inf_assoc, inf_eq_left.2 hc.le_J_H]
  rw [centralizer_coe_eq_centralizer_singleton hbgen, h1, hc.inf_centralizer_eq_W2 b hbB hb1,
    inf_eq_right.2 hc.le_H_W2]

theorem not_le_centralizer_H : ¬ U ≤ centralizer (H : Set M) :=
  have := hc.normal_H
  have := hc.normal_J
  have := hc.isNilpotent_H
  have := hc.isNilpotent_U
  not_le_centralizer_of_isMaximalNilpotentNormalHall hc.hall_H hc.max_H hc.isComplement'_J_B
    hc.hall_B hc.sup_eq_J hc.disjoint_H_U hc.ne_bot_U

theorem commutator_U_le_centralizer_H : ⁅U, U⁆ ≤ centralizer (H : Set M) := by
  have := hc.isNilpotent_F
  have hHF : H ≤ F := hc.max_F H hc.isNilpotent_H hc.normal_H
  have hUUF : ⁅U, U⁆ ≤ F :=
    (Subgroup.commutator_mono hc.le_J_U hc.le_J_U).trans hc.commutator_J_le_F
  have hcop : (Nat.card (⁅U, U⁆ : Subgroup M)).Coprime (Nat.card H) :=
    (hc.coprime_natCard_H_sup.coprime_dvd_right
      ((Subgroup.card_dvd_of_le (Subgroup.commutator_le_self U)).trans
        (Subgroup.card_dvd_of_le le_sup_left))).symm
  have hcop' : (Nat.card ((⁅U, U⁆ : Subgroup M).subgroupOf F)).Coprime
      (Nat.card (H.subgroupOf F)) := by
    rwa [natCard_subgroupOf hUUF, natCard_subgroupOf hHF]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hcomm := commute_of_coprime_natCard hcop' (r := ⟨x, hUUF hx⟩) (s := ⟨h, hHF hh⟩)
    (Subgroup.mem_subgroupOf.2 hx) (Subgroup.mem_subgroupOf.2 hh)
  simpa using (Subtype.ext_iff.mp hcomm).symm

theorem commute_of_mem_commutator_U {x h : M} (hx : x ∈ ⁅U, U⁆) (hh : h ∈ H) : Commute x h :=
  (Subgroup.mem_centralizer_iff.mp (hc.commutator_U_le_centralizer_H hx) h hh).symm

end IsPTypeConfig

end

end CFSG.FeitThompson
