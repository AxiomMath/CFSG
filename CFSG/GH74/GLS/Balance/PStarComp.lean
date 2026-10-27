module

public import CFSG.GH74.GLS.Balance.PStarLayer

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem IsPStar.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {p : ℕ}
    [Fact p.Prime] (h : IsPStar p Y) : IsPStar p Y' := by
  refine ⟨?_, fun N' hN' P' => ?_⟩
  ·
    have h1 : oResidual p Y' = (oResidual p Y).map e.toMonoidHom := by
      unfold oResidual
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        show Nat.Coprime (orderOf (e.symm y)) p
        rw [MulEquiv.orderOf_eq]; exact hy
      · rintro ⟨z, hz, rfl⟩
        show Nat.Coprime (orderOf (e z)) p
        rw [MulEquiv.orderOf_eq]; exact hz
    rw [h1, h.1, Subgroup.map_top_of_surjective _ e.surjective]
  ·
    set N : Subgroup Y := N'.comap e.toMonoidHom with hN
    have hNn : N.Normal := hN'.comap e.toMonoidHom
    have hmap : N.map e.toMonoidHom = N' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective N'
    let φ : ↥N ≃* ↥N' := (e.subgroupMap N).trans (MulEquiv.subgroupCongr hmap)
    have hφ : ∀ n : ↥N, ((φ n : ↥N') : Y') = e (n : Y) := fun n => rfl
    obtain ⟨Q, hQ⟩ := Sylow.exists_comap_eq_of_injective P' (f := φ.symm.toMonoidHom)
      φ.symm.injective
    have htop := h.2 N hNn Q
    have hS : ∀ y : Y, y ∈ (Q : Subgroup ↥N).map N.subtype →
        e y ∈ (P' : Subgroup ↥N').map N'.subtype := by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨φ q, ?_, rfl⟩
      rw [← hQ]
      show φ.symm (φ q) ∈ (Q : Subgroup ↥N)
      have e : φ.symm (φ q) = q := φ.symm_apply_apply q
      rw [e]; exact hq
    have hS' : ∀ y : Y, e y ∈ (P' : Subgroup ↥N').map N'.subtype →
        y ∈ (Q : Subgroup ↥N).map N.subtype := by
      rintro y ⟨p', hp', hp'e⟩
      rw [← hQ] at hp'
      have hq : φ.symm p' ∈ (Q : Subgroup ↥N) := hp'
      refine ⟨φ.symm p', hq, ?_⟩
      apply e.injective
      rw [← hp'e]
      have := hφ (φ.symm p')
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [eq_top_iff]
    intro y' _
    have hy : e.symm y' ∈ N ⊔ centralizer (((Q : Subgroup ↥N).map N.subtype : Subgroup Y) : Set Y) := by
      rw [htop]; exact Subgroup.mem_top _
    have := hNn
    obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hy'e : y' = e n * e c := by
      rw [← map_mul, hnc]; simp
    rw [hy'e]
    refine mul_mem_sup hn ?_
    rw [mem_centralizer_iff]
    intro s' hs'
    obtain ⟨s, hs⟩ : ∃ s : Y, e s = s' := ⟨e.symm s', by simp⟩
    rw [← hs] at hs' ⊢
    have hsS := hS' s hs'
    have := mem_centralizer_iff.mp hc s hsS
    rw [← map_mul, ← map_mul, this]

theorem isPStar_of_isQuasisimple {G : Type} [Group G] [Finite G]
    (hG : IsQuasisimple G) : IsPStar 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : IsComponent (⊤ : Subgroup G) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := G)).symm hG,
      Subgroup.IsSubnormal.top⟩
  have hlayer : layer G = ⊤ :=
    top_le_iff.mp (LocalCores.component_le_layer hcomp)
  have h1 : IsPStar 2 ↥(layer G) := isPStar_layer G
  rw [hlayer] at h1
  exact IsPStar.of_mulEquiv (Subgroup.topEquiv (G := G)) h1

end CFSG.GH74.GLS.Balance
