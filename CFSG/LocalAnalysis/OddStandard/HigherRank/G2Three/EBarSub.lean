module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup
open scoped commutatorElement

theorem subnormal_map_center_centralizer {E : Type*} [Group E] (u : E) (K : Subgroup E)
    (hK : K ≤ centralizer ({u} : Set E))
    (hKn : (K.subgroupOf (centralizer ({u} : Set E))).Normal) :
    ((K.map (QuotientGroup.mk' (center E))).subgroupOf
      (centralizer ({QuotientGroup.mk' (center E) u} : Set (E ⧸ center E)))).IsSubnormal := by
  let π : E →* E ⧸ center E := QuotientGroup.mk' (center E)
  let H : Subgroup E := (centralizer ({π u} : Set (E ⧸ center E))).comap π
  let C : Subgroup E := centralizer ({u} : Set E)
  have key : ∀ h : ↥H, ⁅(h : E), u⁆ ∈ center E := by
    intro h
    have hmem : π (h : E) ∈ centralizer ({π u} : Set (E ⧸ center E)) := h.2
    have hcomm : π (h : E) * π u = π u * π (h : E) :=
      ((Subgroup.mem_centralizer_iff.mp hmem) (π u) (Set.mem_singleton _)).symm
    have h1 : π (⁅(h : E), u⁆) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [← QuotientGroup.eq_one_iff]
    change π ⁅(h : E), u⁆ = 1
    exact h1
  let ψ : ↥H →* ↥(center E) :=
    { toFun := fun h => ⟨⁅(h : E), u⁆, key h⟩,
      map_one' := by
        apply Subtype.ext
        simp,
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅(a : E) * (b : E), u⁆ = ⁅(a : E), u⁆ * ⁅(b : E), u⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hc : (a : E) * ⁅(b : E), u⁆ * (a : E)⁻¹ = ⁅(b : E), u⁆ := by
          rw [Subgroup.mem_center_iff.mp (key b) (a : E), mul_assoc, mul_inv_cancel, mul_one]
        rw [hc]
        exact Subgroup.mem_center_iff.mp (key a) ⁅(b : E), u⁆ }
  have hψ : ∀ h : ↥H, (ψ h : E) = ⁅(h : E), u⁆ := fun h => rfl
  have hker : ψ.ker = C.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ x = 1 ↔ (x : E) ∈ centralizer ({u} : Set E)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hx1 : ⁅(x : E), u⁆ = 1 := by
        have h' := congrArg (fun z : ↥(center E) => (z : E)) hx
        simpa [hψ x] using h'
      show u * (x : E) = (x : E) * u
      exact (commutatorElement_eq_one_iff_mul_comm.mp hx1).symm
    · intro hx
      apply Subtype.ext
      show ⁅(x : E), u⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hx u (Set.mem_singleton u)).symm
  have hCnorm : (C.subgroupOf H).Normal := by
    rw [← hker]
    infer_instance
  have hle : K.subgroupOf H ≤ C.subgroupOf H := by
    intro x hx
    exact hK hx
  have hN : ((K.subgroupOf H).subgroupOf (C.subgroupOf H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff hK).mp hKn h.1 k.1 hh hk
  have hsub : (K.subgroupOf H).IsSubnormal :=
    Subgroup.IsSubnormal.step (K.subgroupOf H) (C.subgroupOf H) hle
      (Subgroup.Normal.isSubnormal hCnorm) hN
  let φ : ↥H →* ↥(centralizer ({π u} : Set (E ⧸ center E))) :=
    { toFun := fun h => ⟨π (h : E), h.2⟩,
      map_one' := by
        apply Subtype.ext
        simp,
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective (center E) (y : E ⧸ center E)
    have heπ : π e = (y : E ⧸ center E) := he
    refine ⟨⟨e, ?_⟩, ?_⟩
    · show π e ∈ centralizer ({π u} : Set (E ⧸ center E))
      rw [heπ]
      exact y.2
    · apply Subtype.ext
      show π e = (y : E ⧸ center E)
      exact heπ
  have hmap : (K.subgroupOf H).map φ =
      (K.map π).subgroupOf (centralizer ({π u} : Set (E ⧸ center E))) := by
    apply Subgroup.ext
    intro x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h.1, hh, rfl⟩
    · rintro ⟨k, hk, hkπ⟩
      refine ⟨⟨k, ?_⟩, hk, ?_⟩
      · show π k ∈ centralizer ({π u} : Set (E ⧸ center E))
        rw [hkπ]
        exact x.2
      · apply Subtype.ext
        show π k = x.1
        exact hkπ
  change ((K.map π).subgroupOf (centralizer ({π u} : Set (E ⧸ center E)))).IsSubnormal
  rw [← hmap]
  exact hsub.map hφsurj

end CFSG.OddStandard.HigherRank.G2Three
