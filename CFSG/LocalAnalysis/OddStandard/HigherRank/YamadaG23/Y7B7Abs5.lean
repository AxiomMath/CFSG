module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7b_fpf_onto {U M : Subgroup G} (hMU : M ≤ U)
    (hMnorm : ∀ u ∈ U, ∀ m ∈ M, u * m * u⁻¹ ∈ M) (hab : ∀ u ∈ U, ∀ v ∈ U, ⁅u, v⁆ ∈ M) {k : G}
    (hkU : ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hkM : ∀ m ∈ M, k * m * k⁻¹ ∈ M)
    (hfix : ∀ u ∈ U, u⁻¹ * (k * u * k⁻¹) ∈ M → u ∈ M) :
    ∀ v ∈ U, ∃ u ∈ U, v⁻¹ * (u * (k * u * k⁻¹)⁻¹) ∈ M := by
  have hMnormal : (M.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hMU).mpr fun m u hm hu => hMnorm u hu m hm
  letI : (M.subgroupOf U).Normal := hMnormal
  let Q := ↥U ⧸ (M.subgroupOf U)
  haveI hQcomm : IsMulCommutative Q := by
    change IsMulCommutative (↥U ⧸ (M.subgroupOf U))
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, _root_.commutator_def,
      Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    change ⁅(a : G), (b : G)⁆ ∈ M
    exact hab (a : G) a.2 (b : G) b.2
  let σU : ↥U →* ↥U :=
    { toFun := fun u => ⟨k * (u : G) * k⁻¹, hkU (u : G) u.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hσU : M.subgroupOf U ≤ (M.subgroupOf U).comap σU := by
    intro m hm
    rw [Subgroup.mem_subgroupOf] at hm
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hkM (m : G) hm
  let σ : Q →* Q := QuotientGroup.map (M.subgroupOf U) (M.subgroupOf U) σU hσU
  have hσmk : ∀ u : ↥U, σ (QuotientGroup.mk' (M.subgroupOf U) u) =
      QuotientGroup.mk' (M.subgroupOf U) (σU u) := fun _ => rfl
  let f : Q →* Q := MonoidHom.id Q * (invMonoidHom.comp σ)
  have hf : ∀ q : Q, f q = q * (σ q)⁻¹ := fun _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    rw [hf] at hq
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf U) q
    have hq' : QuotientGroup.mk' (M.subgroupOf U) u =
        QuotientGroup.mk' (M.subgroupOf U) (σU u) := by
      have h := mul_inv_eq_one.mp hq
      rwa [hσmk u] at h
    have hmem : (u : G)⁻¹ * (k * (u : G) * k⁻¹) ∈ M := by
      have h := (QuotientGroup.eq (s := M.subgroupOf U) (a := u) (b := σU u)).mp hq'
      rw [Subgroup.mem_subgroupOf] at h
      change (u : G)⁻¹ * (k * (u : G) * k⁻¹) ∈ M at h
      exact h
    have huM : (u : G) ∈ M := hfix (u : G) u.2 hmem
    exact (QuotientGroup.eq_one_iff (N := M.subgroupOf U) u).mpr
      (by rw [Subgroup.mem_subgroupOf]; exact huM)
  have hsurj : Function.Surjective f :=
    haveI hQfin : Finite Q :=
      Finite.of_surjective (QuotientGroup.mk' (M.subgroupOf U))
        (QuotientGroup.mk'_surjective (M.subgroupOf U))
    Finite.injective_iff_surjective.mp hinj
  intro v hv
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk' (M.subgroupOf U) ⟨v, hv⟩)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf U) q
  refine ⟨u, u.2, ?_⟩
  rw [hf] at hq
  have hq' : QuotientGroup.mk' (M.subgroupOf U) (u * (σU u)⁻¹) =
      QuotientGroup.mk' (M.subgroupOf U) (⟨v, hv⟩ : ↥U) := by
    rw [hσmk u] at hq
    rw [← map_inv, ← map_mul] at hq
    exact hq
  have hone : QuotientGroup.mk' (M.subgroupOf U)
      ((⟨v, hv⟩ : ↥U)⁻¹ * (u * (σU u)⁻¹)) = 1 := by
    rw [map_mul, map_inv, hq', inv_mul_cancel]
  have hmemN := (QuotientGroup.eq_one_iff (N := M.subgroupOf U)
    ((⟨v, hv⟩ : ↥U)⁻¹ * (u * (σU u)⁻¹))).mp hone
  rw [Subgroup.mem_subgroupOf] at hmemN
  change v⁻¹ * ((u : G) * (k * (u : G) * k⁻¹)⁻¹) ∈ M at hmemN
  exact hmemN

end CFSG.OddStandard.HigherRank.YamadaG23
