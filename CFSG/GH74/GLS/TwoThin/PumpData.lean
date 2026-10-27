module

public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.GH74.GLS.TwoThin.Cover
public import CFSG.GH74.GLS.TwoThin.OddOrbit

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {x y : G}

omit [Finite G] in
theorem mem_centralizer_symm (h : y ∈ centralizer ({x} : Set G)) :
    x ∈ centralizer ({y} : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at h ⊢
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact (h x (Set.mem_singleton x)).symm

omit [Finite G] in
theorem orderOf_mk_centralizer (hxy : x ∈ centralizer ({y} : Set G)) (hx : orderOf x = 2) :
    orderOf (⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact hx

theorem isTwoComponent_subgroupOf_congr {Z : Type*} [Group Z] [Finite Z] {A B B' : Subgroup Z}
    (h : B = B') (hA : TwoComponents.IsTwoComponent (A.subgroupOf B)) :
    TwoComponents.IsTwoComponent (A.subgroupOf B') := by
  subst h
  exact hA

omit [Finite G] in
theorem le_centralizer_mk {Λ : Subgroup G}
    (hΛW : Λ ≤ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))
    (hxy : x ∈ centralizer ({y} : Set G)) :
    Λ.subgroupOf (centralizer ({y} : Set G)) ≤
      centralizer ({(⟨x, hxy⟩ : ↥(centralizer ({y} : Set G)))} :
        Set ↥(centralizer ({y} : Set G))) := by
  rw [centralizer_singleton_eq_subgroupOf hxy]
  intro a ha
  exact Subgroup.mem_subgroupOf.mpr (hΛW (Subgroup.mem_subgroupOf.mp ha))

theorem isTwoComponent_centralizer_mk {Λ : Subgroup G}
    (hΛW : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) Λ)
    (hxy : x ∈ centralizer ({y} : Set G)) :
    TwoComponents.IsTwoComponent
      ((Λ.subgroupOf (centralizer ({y} : Set G))).subgroupOf
        (centralizer ({(⟨x, hxy⟩ : ↥(centralizer ({y} : Set G)))} :
          Set ↥(centralizer ({y} : Set G))))) :=
  isTwoComponent_subgroupOf_congr (centralizer_singleton_eq_subgroupOf hxy).symm
    (isTwoComponent_subgroupOf_subgroupOf hΛW.1 inf_le_right (isPCompIn_two_iff.mp hΛW).2)

omit [Finite G] in
theorem isSubnormal_inf_subgroupOf {C K W : Subgroup G} (hK : (K.subgroupOf C).IsSubnormal)
    (hWC : W ≤ C) : (K.subgroupOf W).IsSubnormal := by
  have := hK.comap (Subgroup.inclusion hWC)
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

theorem pumpup_cover {K : Subgroup G} (hy : orderOf y = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hyK : y ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    ∃ Λ : Subgroup G, Λ ≤ K ⊓ centralizer ({y} : Set G) ∧
      pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) = Λ ∧
      IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) Λ ∧
      (∀ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L → L = Λ) ∧
      IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) Λ ∧
      (∀ z ∈ K ⊓ centralizer ({y} : Set G), (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ Λ) ∧
      (∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) := by
  have hXK : K ⊓ centralizer ({y} : Set G) ≤ K := inf_le_left
  have hcov : ∀ k ∈ K, ∃ c ∈ K ⊓ centralizer ({y} : Set G), ∃ o ∈ pPrimeCoreOf 2 K, k = c * o :=
    exists_centralizer_mul_pPrimeCore hyK hy
  obtain ⟨Λ, hΛX, hpc, huniqL, hlayer, h2el, hcovΛ⟩ :=
    cover_data hXK hcov (isQuasisimple_hat hK)
  refine ⟨Λ, hΛX, hlayer, hpc, huniqL, ?_, h2el, hcovΛ⟩
  set W := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hW
  have hXW : K ⊓ centralizer ({y} : Set G) ≤ W := le_inf (hK.1.trans' inf_le_left |>.trans le_rfl)
    inf_le_right
  refine isPCompIn_two_iff.mpr ⟨hΛX.trans hXW, ?_⟩
  have hKsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hK).2.1 Subgroup.IsSubnormal.top
  have hsub : ((K ⊓ centralizer ({y} : Set G)).subgroupOf W).IsSubnormal := by
    have h1 := isSubnormal_inf_subgroupOf hKsub (inf_le_left : W ≤ centralizer ({x} : Set G))
    have h2 : (K ⊓ centralizer ({y} : Set G)).subgroupOf W = K.subgroupOf W := by
      ext a
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp a.2).2⟩⟩
    rwa [h2]
  exact TwoComponentTransport.extend_nested Λ _ W hΛX hXW hsub (isPCompIn_two_iff.mp hpc).2

omit [Finite G] in
theorem pumpUp_le_centralizer (K : Subgroup G) (y : G) :
    pumpUp 2 K y ≤ centralizer ({y} : Set G) := by
  rw [pumpUp_eq_map_pumpupY]
  exact Subgroup.map_subtype_le _

theorem isTwoComponent_of_isPCompIn_pumpUp {K K' Λ : Subgroup G}
    (hΛlayer : pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) = Λ)
    (hΛE : Λ.subgroupOf (centralizer ({y} : Set G)) ≤
      TwoLayer.subgroup ↥(centralizer ({y} : Set G)))
    (hK' : IsPCompIn 2 (pumpUp 2 K y) K') :
    TwoComponents.IsTwoComponent (K'.subgroupOf (centralizer ({y} : Set G))) ∧
      K'.subgroupOf (centralizer ({y} : Set G)) ≤
        pumpupY (Λ.subgroupOf (centralizer ({y} : Set G))) := by
  have hJ : pumpUp 2 K y = (pumpupY (Λ.subgroupOf (centralizer ({y} : Set G)))).map
      (centralizer ({y} : Set G)).subtype := by
    rw [pumpUp_eq_map_pumpupY, hΛlayer]
  have hJY : (pumpUp 2 K y).subgroupOf (centralizer ({y} : Set G)) =
      pumpupY (Λ.subgroupOf (centralizer ({y} : Set G))) := by
    rw [hJ]
    exact Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set G)).subtype_injective _
  have hJle : pumpUp 2 K y ≤ centralizer ({y} : Set G) := pumpUp_le_centralizer K y
  have hsub : ((pumpUp 2 K y).subgroupOf (centralizer ({y} : Set G))).IsSubnormal := by
    rw [hJY]
    exact isSubnormal_pumpupY hΛE
  obtain ⟨hK'J, hK'p⟩ := hK'
  have hK'2 : TwoComponents.IsTwoComponent (K'.subgroupOf (pumpUp 2 K y)) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hK'p
  refine ⟨TwoComponentTransport.extend_nested K' (pumpUp 2 K y) _ hK'J hJle hsub hK'2, ?_⟩
  rw [← hJY]
  intro a ha
  exact Subgroup.mem_subgroupOf.mpr (hK'J (Subgroup.mem_subgroupOf.mp ha))

end CFSG.GH74.GLS.TwoThin
