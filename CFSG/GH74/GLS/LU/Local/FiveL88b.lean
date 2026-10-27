module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.GH74.GLS.LU.Local.FiveZstar

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Gen88

variable {G : Type} [Group G] [Finite G]

@[expose] def QQ (E : Subgroup G) : Subgroup G :=
  (CFSG.oddCore ↥(normalizer (E : Set G))).map (normalizer (E : Set G)).subtype

omit [Finite G] in
theorem QQ_le (E : Subgroup G) : QQ E ≤ normalizer (E : Set G) := Subgroup.map_subtype_le _

theorem QQ_odd (E : Subgroup G) : Odd (Nat.card ↥(QQ E)) := by
  rw [QQ, Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (normalizer (E : Set G)).subtype_injective).toEquiv.symm]
  exact odd_card_oddCore' _

omit [Finite G] in
theorem normalizer_le_normalizer_QQ (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer ((QQ E : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨o, ho, rfl⟩
    have := (inferInstance : (CFSG.oddCore ↥(normalizer (E : Set G))).Normal).conj_mem o ho ⟨x, hx⟩
    exact ⟨_, this, rfl⟩
  · rintro ⟨o, ho, hoy⟩
    have := (inferInstance : (CFSG.oddCore ↥(normalizer (E : Set G))).Normal).conj_mem o ho
      ⟨x, hx⟩⁻¹
    refine ⟨_, this, ?_⟩
    have h2 : (o : G) = x * y * x⁻¹ := hoy
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, h2]
    group

omit [Finite G] in
theorem le_QQ {E : Subgroup G} (hodd : Odd (Nat.card ↥E)) : E ≤ QQ E := by
  intro e he
  have hnorm : (E.subgroupOf (normalizer (E : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hodd' : Odd (Nat.card ↥(E.subgroupOf (normalizer (E : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact hodd
  have hle : E.subgroupOf (normalizer (E : Set G)) ≤ CFSG.oddCore ↥(normalizer (E : Set G)) :=
    le_sSup ⟨hnorm, hodd'⟩
  have hmem : (⟨e, Subgroup.le_normalizer he⟩ : ↥(normalizer (E : Set G))) ∈
      E.subgroupOf (normalizer (E : Set G)) := he
  exact ⟨_, hle hmem, rfl⟩

omit [Finite G] in
theorem le_QQ_of_normal {E M : Subgroup G} (hME : M ≤ normalizer (E : Set G))
    (hnorm : M.subgroupOf (normalizer (E : Set G)) |>.Normal) (hodd : Odd (Nat.card ↥M)) :
    M ≤ QQ E := by
  intro e he
  have hodd' : Odd (Nat.card ↥(M.subgroupOf (normalizer (E : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hME).toEquiv]
    exact hodd
  have hle : M.subgroupOf (normalizer (E : Set G)) ≤ CFSG.oddCore ↥(normalizer (E : Set G)) :=
    le_sSup ⟨hnorm, hodd'⟩
  have hmem : (⟨e, hME he⟩ : ↥(normalizer (E : Set G))) ∈ M.subgroupOf (normalizer (E : Set G)) :=
    he
  exact ⟨_, hle hmem, rfl⟩

end Gen88

end CFSG.GH74.GLS.LU.Local.Five
