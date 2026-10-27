module

public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools

section Aux

variable {G : Type} [Group G]

theorem exists_mem_conjugate_le_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P K R : Subgroup G}
    (hP : IsSylowOf p P K) (hRK : R ≤ K) (hR : IsPGroup p R) :
    ∃ k ∈ K, conjugate R k ≤ P := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy1 : (c : G) * y * (c : G)⁻¹ ∈ R := mem_conjugate_iff'.1 hy
  have hy' : (⟨(c : G) * y * (c : G)⁻¹, hRK hy1⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) :=
    hQ' hy1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  refine ⟨_, hy', ?_⟩
  simp [MulAut.inv_apply]
  group

theorem isSylowOf_conjugate [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) : IsSylowOf p (conjugate P g) (conjugate K g) :=
  isSylowOf_of_card (conjugate_le_conjugate' h.le g)
    (by rw [card_conjugate', card_conjugate', h.card_eq])

theorem conjugate_centralizer_singleton (x g : G) :
    conjugate (centralizer ({x} : Set G)) g = centralizer ({g⁻¹ * x * g} : Set G) := by
  ext z
  rw [mem_conjugate_iff', mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * (g⁻¹ * x * g) = g⁻¹ * ((g * z * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * z := by group
  · intro h
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * z) * g⁻¹ := by rw [h]
      _ = x * (g * z * g⁻¹) := by group

end Aux

theorem iv2_3_2 {G : Type} [Group G] [Finite G] {x : G} {T W : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hWT : W ≤ T)
    (hwc : ∀ g : G, CFSG.conjugate W g ≤ T → CFSG.conjugate W g = W) {y : G}
    (hy : y ∈ centralizer (W : Set G) ⊓ T) {g : G} (hg : y = g⁻¹ * x * g) :
    ∃ n ∈ normalizer (W : Set G), y = n⁻¹ * x * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTg : IsSylowOf 2 (conjugate T g) (centralizer ({y} : Set G)) := by
    have h := isSylowOf_conjugate hT g
    rwa [conjugate_centralizer_singleton, ← hg] at h
  have hWy : W ≤ centralizer ({y} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hy.1 w hw)
  obtain ⟨c, hc, hcW⟩ := exists_mem_conjugate_le_of_isSylowOf hTg hWy (hT.isPGroup.to_le hWT)
  have hle : conjugate W (c * g⁻¹) ≤ T := by
    rw [conjugate_mul']
    have h := conjugate_le_conjugate' hcW g⁻¹
    rwa [conjugate_inv_conjugate'] at h
  have heq : conjugate W (c * g⁻¹) = W := hwc _ hle
  have hm : c * g⁻¹ ∈ normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 : w ∈ conjugate W (c * g⁻¹) ↔ w ∈ W := by rw [heq]
    rw [mem_conjugate_iff'] at h1
    exact h1.symm
  refine ⟨(c * g⁻¹)⁻¹, (normalizer (W : Set G)).inv_mem hm, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hc
  calc y = c * y * c⁻¹ := by rw [hcy]; group
    _ = ((c * g⁻¹)⁻¹)⁻¹ * x * (c * g⁻¹)⁻¹ := by rw [hg]; group

end CFSG.GH74.GLS.C3.Layer1.Back
