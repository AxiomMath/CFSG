module

public import CFSG.FeitThompson.Definitions.DadeData
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {G : Type*} [Group G]

theorem mem_conj_smul_iff {l x : G} {X : Subgroup G} :
    x ∈ MulAut.conj l • X ↔ l⁻¹ * x * l ∈ X := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

theorem smul_centralizer_singleton (l a : G) :
    MulAut.conj l • Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer ({l * a * l⁻¹} : Set G) := by
  ext x
  rw [mem_conj_smul_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (l * a * l⁻¹) = l * (l⁻¹ * x * l * a) * l⁻¹ := by group
      _ = l * (a * (l⁻¹ * x * l)) * l⁻¹ := by rw [h]
      _ = l * a * l⁻¹ * x := by group
  · intro h
    calc l⁻¹ * x * l * a = l⁻¹ * (x * (l * a * l⁻¹)) * l := by group
      _ = l⁻¹ * (l * a * l⁻¹ * x) * l := by rw [h]
      _ = a * (l⁻¹ * x * l) := by group

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a : G}

theorem conj_smul_H_le_centralizer (hD : IsDadeData L A H) (ha : a ∈ A) (l : G) :
    MulAut.conj l • H a ≤ Subgroup.centralizer ({l * a * l⁻¹} : Set G) := by
  rw [← smul_centralizer_singleton]
  intro x hx
  exact mem_conj_smul_iff.2 (hD.le_centralizer ha (mem_conj_smul_iff.1 hx))

theorem normal_subgroupOf_conj_smul_H (hD : IsDadeData L A H) (ha : a ∈ A) (l : G) :
    ((MulAut.conj l • H a).subgroupOf
      (Subgroup.centralizer ({l * a * l⁻¹} : Set G))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (hD.conj_smul_H_le_centralizer ha l)).2 ?_
  intro h k hh hk
  refine mem_conj_smul_iff.2 ?_
  have hh' : l⁻¹ * h * l ∈ H a := mem_conj_smul_iff.1 hh
  have hk' : l⁻¹ * k * l ∈ Subgroup.centralizer ({a} : Set G) :=
    mem_conj_smul_iff.1 (by rwa [smul_centralizer_singleton])
  have hconj := hD.conj_mem_H ha hk' hh'
  have hrw : l⁻¹ * (k * h * k⁻¹) * l
      = (l⁻¹ * k * l) * (l⁻¹ * h * l) * (l⁻¹ * k * l)⁻¹ := by group
  rwa [hrw]

omit [Finite G] in
theorem card_conj_smul_H (l : G) : Nat.card ↥(MulAut.conj l • H a) = Nat.card ↥(H a) :=
  natCard_conj_smul l (H a)

theorem index_subgroupOf_conj_smul_H (hD : IsDadeData L A H) (ha : a ∈ A) (l : G) :
    ((MulAut.conj l • H a).subgroupOf
        (Subgroup.centralizer ({l * a * l⁻¹} : Set G))).index =
      ((H a).subgroupOf (Subgroup.centralizer ({a} : Set G))).index := by
  have h1 := Subgroup.index_mul_card ((MulAut.conj l • H a).subgroupOf
    (Subgroup.centralizer ({l * a * l⁻¹} : Set G)))
  have h2 := Subgroup.index_mul_card ((H a).subgroupOf (Subgroup.centralizer ({a} : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hD.conj_smul_H_le_centralizer ha l)).toEquiv,
    card_conj_smul_H (H := H) l] at h1
  rw [hD.card_subgroupOf_H ha] at h2
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H a)) ?_
  rw [h1, h2, ← smul_centralizer_singleton, natCard_conj_smul]

theorem conj_smul_H (hD : IsDadeData L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    H (l * a * l⁻¹) = MulAut.conj l • H a := by
  refine (hD.eq_H_of_normal (hD.conj_mem ha hl) (hD.conj_smul_H_le_centralizer ha l)
    (hD.normal_subgroupOf_conj_smul_H ha l) ?_ ?_).symm
  · rw [card_conj_smul_H (H := H) l]; exact hD.isPiNumber_compl_card_H ha
  · rw [hD.index_subgroupOf_conj_smul_H ha l]; exact hD.isPiNumber_index_subgroupOf_H ha

theorem conj_inv_smul_H (hD : IsDadeData L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    H (l⁻¹ * a * l) = MulAut.conj l⁻¹ • H a := by
  simpa using hD.conj_smul_H ha (inv_mem hl)

end IsDadeData

end

end CFSG.FeitThompson
