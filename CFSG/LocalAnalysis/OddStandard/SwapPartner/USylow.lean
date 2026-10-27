module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup
open scoped Pointwise

theorem exists_conj_le_of_forall_card_le {G : Type*} [Group G] [Finite G] {Y D U : Subgroup G}
    {k : ℕ} (hDY : D ≤ Y) (hD : Nat.card ↥D = 2 ^ k)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Y → Nat.card ↥Q ≤ 2 ^ k)
    (hU : IsPGroup 2 U) (hUY : U ≤ Y) : ∃ c ∈ Y, ∀ u ∈ U, c * u * c⁻¹ ∈ D := by
  let D' : Subgroup ↥Y := D.subgroupOf Y
  have hD'card : Nat.card ↥D' = 2 ^ k := by
    rw [show Nat.card ↥D' = Nat.card ↥D from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv]
    exact hD
  have hD'pg : IsPGroup 2 D' := IsPGroup.of_card hD'card
  have hPmax : ∀ {Q : Subgroup ↥Y}, IsPGroup 2 Q → D' ≤ Q → Q = D' := by
    intro Q hQ hDQ
    have hQmap_pg : IsPGroup 2 (Q.map Y.subtype) := hQ.map Y.subtype
    have hQmap_le : Q.map Y.subtype ≤ Y := by
      rintro _ ⟨q, _, rfl⟩
      exact q.2
    have hcard_map : Nat.card ↥(Q.map Y.subtype) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective (K := Q) (f := Y.subtype) Y.subtype_injective
    have hQle : Nat.card ↥Q ≤ 2 ^ k := by
      rw [← hcard_map]
      exact hmax (Q.map Y.subtype) hQmap_pg hQmap_le
    have hD'le : Nat.card ↥D' ≤ Nat.card ↥Q := Subgroup.card_le_of_le hDQ
    have hcard_eq : Nat.card ↥Q = Nat.card ↥D' :=
      le_antisymm (by rw [hD'card]; exact hQle) hD'le
    exact (Subgroup.eq_of_le_of_card_ge hDQ hcard_eq.le).symm
  let P : Sylow 2 ↥Y :=
    { toSubgroup := D'
      isPGroup' := hD'pg
      is_maximal' := fun {Q} hQ hDQ => hPmax hQ hDQ }
  let U' : Subgroup ↥Y := U.subgroupOf Y
  have hU'pg : IsPGroup 2 U' := hU.comap_subtype
  obtain ⟨Q, hU'Q⟩ := hU'pg.exists_le_sylow
  haveI : Finite (Sylow 2 ↥Y) := Sylow.finite_of_finiteIndex P
  obtain ⟨c₀, hc₀⟩ := MulAction.exists_smul_eq (M := ↥Y) P Q
  refine ⟨((c₀⁻¹ : ↥Y) : G), (c₀⁻¹ : ↥Y).2, ?_⟩
  intro u hu
  let y : ↥Y := ⟨u, hUY hu⟩
  have hyU' : y ∈ U' := by
    rw [show U' = U.subgroupOf Y from rfl, Subgroup.mem_subgroupOf]
    exact hu
  have hyQ : y ∈ Q := hU'Q hyU'
  have hsub : (MulAut.conj c₀) • (P : Subgroup ↥Y) = (Q : Subgroup ↥Y) := by
    have h := congrArg (fun S : Sylow 2 ↥Y => (S : Subgroup ↥Y)) hc₀
    simpa only [Sylow.coe_subgroup_smul] using h
  have hyconj : c₀⁻¹ * y * c₀ ∈ (P : Subgroup ↥Y) := by
    have h1 : (MulAut.conj c₀)⁻¹ • y ∈ (P : Subgroup ↥Y) := by
      apply Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp
      rw [hsub]
      exact hyQ
    simpa only [MulAut.smul_def, MulAut.conj_inv_apply] using h1
  have hmem : ((c₀⁻¹ * y * c₀ : ↥Y) : G) ∈ D := by
    change c₀⁻¹ * y * c₀ ∈ D.subgroupOf Y at hyconj
    rwa [Subgroup.mem_subgroupOf] at hyconj
  simpa [y] using hmem

end CFSG.OddStandard.AltStdSec.SwapPartner
