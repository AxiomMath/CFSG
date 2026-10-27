module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.SwapData
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

structure AlmostSimpleLocal (T : Type*) [Group T] (u : T) : Prop where
  orderOf_eq : orderOf u = 2
  exists_alt : ∃ K : Subgroup T, K ≤ centralizer ({u} : Set T) ∧
    Nonempty (↥K ≃* alternatingGroup (Fin 5))
  card_dvd : Nat.card ↥(centralizer ({u} : Set T)) ∣ 960

theorem AlmostSimpleLocal.sixty_dvd {T : Type*} [Group T] {u : T} (h : AlmostSimpleLocal T u) :
    60 ∣ Nat.card ↥(centralizer ({u} : Set T)) := by
  obtain ⟨K, hK, ⟨φ⟩⟩ := h.exists_alt
  have h60 : Nat.card ↥K = 60 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  rw [← h60]
  exact Subgroup.card_dvd_of_le hK

theorem AlmostSimpleLocal.exists_perfect {T : Type*} [Group T] {u : T} (h : AlmostSimpleLocal T u) :
    ∃ K : Subgroup T, K ≤ centralizer ({u} : Set T) ∧ ⁅K, K⁆ = K ∧ Nat.card ↥K = 60 := by
  obtain ⟨K, hK, ⟨φ⟩⟩ := h.exists_alt
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  haveI : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  refine ⟨K, hK, Subgroup.isPerfect_iff.1 inferInstance, ?_⟩
  rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem AlmostSimpleLocal.card_dvd_of_le {T : Type*} [Group T] {u : T} (h : AlmostSimpleLocal T u)
    {H : Subgroup T} (hH : H ≤ centralizer ({u} : Set T)) : Nat.card ↥H ∣ 960 :=
  (Subgroup.card_dvd_of_le hH).trans h.card_dvd

theorem centralizer_singleton_eq_map_of_mulEquiv {T Y : Type*} [Group T] [Group Y] (e : T ≃* Y)
    (u : T) : centralizer ({e u} : Set Y) = (centralizer ({u} : Set T)).map e.toMonoidHom := by
  ext y
  rw [mem_map]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    simpa [map_mul] using hy
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff] at hx ⊢
    simpa [map_mul] using congrArg e hx

theorem card_centralizer_singleton_mulEquiv {T Y : Type*} [Group T] [Group Y] (e : T ≃* Y)
    (u : T) : Nat.card ↥(centralizer ({e u} : Set Y)) = Nat.card ↥(centralizer ({u} : Set T)) := by
  rw [centralizer_singleton_eq_map_of_mulEquiv e u, Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_singleton_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card ↥(centralizer ({a} : Set G)) = Nat.card ↥(centralizer ({b} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := card_centralizer_singleton_mulEquiv (MulAut.conj c) a
  simpa [MulAut.conj_apply] using this.symm

theorem AlmostSimpleLocal.map {T Y : Type*} [Group T] [Group Y] {u : T}
    (h : AlmostSimpleLocal T u) (e : T ≃* Y) : AlmostSimpleLocal Y (e u) := by
  have hmap := centralizer_singleton_eq_map_of_mulEquiv e u
  refine ⟨?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.orderOf_eq
  · obtain ⟨K, hK, ⟨φ⟩⟩ := h.exists_alt
    refine ⟨K.map e.toMonoidHom, ?_, ⟨?_⟩⟩
    · rw [hmap]
      exact Subgroup.map_mono hK
    · exact (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective).symm.trans φ
  · rw [card_centralizer_singleton_mulEquiv e u]
    exact h.card_dvd

theorem card_centralizer_subtype_eq_card_inf {X : Type*} [Group X] {T : Subgroup X} {u : X}
    (huT : u ∈ T) :
    Nat.card ↥(centralizer ({(⟨u, huT⟩ : T)} : Set T)) =
      Nat.card ↥(T ⊓ centralizer ({u} : Set X)) := by
  have hcentralizer : (centralizer ({(⟨u, huT⟩ : T)} : Set T)).map T.subtype =
      T ⊓ centralizer ({u} : Set X) := by
    ext g
    simp only [mem_map, mem_centralizer_singleton_iff, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hgT, hg⟩
      exact ⟨⟨g, hgT⟩, Subtype.ext hg, rfl⟩
  rw [← hcentralizer, Subgroup.card_map_of_injective T.subtype_injective]

theorem AlmostSimpleLocal.of_altCentralizer_le {X : Type*} [Group X] [Finite X] {u : X}
    (hu : u * u = 1) (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {T : Subgroup X} (huT : u ∈ T) (hK : altCentralizer e ≤ T) :
    AlmostSimpleLocal ↥T ⟨u, huT⟩ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_centralizer_subtype_eq_card_inf huT
  have hC960 : Nat.card ↥(centralizer ({u} : Set X)) = 960 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm,
      Nat.card_fin]
    norm_num [Nat.factorial]
  refine ⟨?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · apply Subtype.ext
      simpa [sq] using hu
    · intro h
      exact hu1 (congrArg Subtype.val h)
  · refine ⟨(altCentralizer e).subgroupOf T, ?_, ?_⟩
    · intro k hk
      rw [mem_centralizer_singleton_iff]
      have hkC : (k : X) ∈ centralizer ({u} : Set X) := Subgroup.map_subtype_le _ hk
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hkC)
    · obtain ⟨φ⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
      exact ⟨((Subgroup.subgroupOfEquivOfLe hK).trans
        (Subgroup.equivMapOfInjective _ (centralizer ({u} : Set X)).subtype
          (centralizer ({u} : Set X)).subtype_injective).symm).trans φ⟩
  · rw [hcard, ← hC960]
    exact Subgroup.card_dvd_of_le inf_le_right

end CFSG.EvenSporadicStandard.TwoHS.GH312
