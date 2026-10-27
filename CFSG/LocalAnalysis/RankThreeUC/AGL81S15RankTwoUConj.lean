module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

private theorem map_subgroupOf_normalizerMonoidHom_eq {G : Type} [Group G] {S Ls : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (Ls : Set G)) {s : G} (hs : s ∈ S) :
    ((S ⊓ Ls).subgroupOf Ls).map (Ls.normalizerMonoidHom ⟨s, hSL hs⟩).toMonoidHom =
      (S ⊓ Ls).subgroupOf Ls := by
  have hsN : s ∈ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp hsN (y : G)).1
      (Subgroup.mem_subgroupOf.mp hy)
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa only [MulEquiv.coe_toMonoidHom,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using h)
  · intro hx
    have hsinvN := Subgroup.inv_mem _ hsN
    have hsinvL := Subgroup.inv_mem _ (hSL hs)
    have hmem := (Subgroup.mem_normalizer_iff.mp hsinvN (x : G)).1 hx
    have hmemL := (Subgroup.mem_normalizer_iff.mp hsinvL (x : G)).1 x.2
    refine ⟨⟨s⁻¹ * (x : G) * (s⁻¹)⁻¹, hmemL⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    apply Subtype.ext
    simpa only [MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using
      (show s * (s⁻¹ * (x : G) * (s⁻¹)⁻¹) * s⁻¹ = (x : G) by group)

theorem exists_scalarTorus_of_hasScalarTorus {G : Type} [Group G] {S Ls : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (Ls : Set G)) {q : ℕ}
    (h : HasScalarTorus ↥Ls q ((S ⊓ Ls).subgroupOf Ls)) :
    ∃ E : Subgroup G, E ≤ Ls ∧ E ≤ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G) ∧
      IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      (∀ s ∈ S, ∃ j : ℕ, ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ S ⊓ Ls) ∧
      (∀ s ∈ S, s * s = 1 → ∀ x ∈ E, s * x * s⁻¹ * x⁻¹ ∈ S ⊓ Ls) := by
  classical
  obtain ⟨E₀, hE₀norm, hE₀ab, hE₀card, hE₀scalar⟩ := h
  have hcomap : (Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G)).comap Ls.subtype =
      Subgroup.normalizer (((S ⊓ Ls).subgroupOf Ls : Subgroup Ls) : Set Ls) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simp)
  refine ⟨E₀.map Ls.subtype, Subgroup.map_subtype_le E₀, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ (Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G)).comap Ls.subtype := by
      rw [hcomap]
      exact hE₀norm hy
    exact Subgroup.mem_comap.mp hy'
  · refine ⟨@Subgroup.map_isMulCommutative ↥Ls G _ _ E₀ Ls.subtype hE₀ab.1, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    simpa using congrArg Ls.subtype (hE₀ab.2 y hy)
  · rw [Subgroup.card_map_of_injective Ls.subtype_injective]
    exact hE₀card
  · intro s hs
    obtain ⟨j, hj⟩ := (hE₀scalar (Ls.normalizerMonoidHom ⟨s, hSL hs⟩)
      (map_subgroupOf_normalizerMonoidHom_eq hSL hs)).1
    refine ⟨j, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    have hmem : ((Ls.normalizerMonoidHom ⟨s, hSL hs⟩ y * (y ^ j)⁻¹ : ↥Ls) : G) ∈ S ⊓ Ls :=
      Subgroup.mem_subgroupOf.mp (hj y hy)
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem
  · intro s hs hs2
    have hn : (⟨s, hSL hs⟩ : Subgroup.normalizer (Ls : Set G)) * ⟨s, hSL hs⟩ = 1 := by
      apply Subtype.ext
      simpa using hs2
    have hα2 :
        Ls.normalizerMonoidHom ⟨s, hSL hs⟩ * Ls.normalizerMonoidHom ⟨s, hSL hs⟩ = 1 := by
      have hαeq : Ls.normalizerMonoidHom ⟨s, hSL hs⟩ * Ls.normalizerMonoidHom ⟨s, hSL hs⟩ =
          Ls.normalizerMonoidHom (⟨s, hSL hs⟩ * ⟨s, hSL hs⟩) := by
        rw [map_mul]
      rw [hαeq, hn, map_one]
    rintro x ⟨y, hy, rfl⟩
    have hmem : ((Ls.normalizerMonoidHom ⟨s, hSL hs⟩ y * y⁻¹ : ↥Ls) : G) ∈ S ⊓ Ls :=
      Subgroup.mem_subgroupOf.mp ((hE₀scalar (Ls.normalizerMonoidHom ⟨s, hSL hs⟩)
        (map_subgroupOf_normalizerMonoidHom_eq hSL hs)).2 hα2 y hy)
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem

end CFSG.LocalAnalysis.RankThreeUC.S15

end
