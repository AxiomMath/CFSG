module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyConj
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Defs
public import CFSG.ClassicalGroups.Alternating.I4SpPlaneConj

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem I4Setting.isLongRootElement_map_of_isPlane (hs : I4Setting hBN Qf ρ)
    {π : Submodule K N} (hπ : IsPlane BN π) {g : Gsp BN} (hg : g ∈ planeGroup hBN π)
    (hg1 : g ≠ 1) : IsLongRootElement Qf (ρ g) := by
  obtain ⟨a, ha, c, hc, hind, rfl⟩ := eq_lineElt_of_mem_planeGroup hBN hs.nondegN hπ hg hg1
  exact hs.siegel a c (hπ.1 a ha c hc) hind

theorem I4Setting.isLongRootElement_map_of_isLine (hs : I4Setting hBN Qf ρ)
    {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {g : Gsp BN} (hg : g ∈ planeGroup hBN ℓ)
    (hg1 : g ≠ 1) : IsLongRootElement Qf (ρ g) := by
  obtain ⟨a, c, hac, hind, rfl⟩ := hℓ.exists_pair
  rw [planeGroup_span_pair hBN hac] at hg
  obtain ⟨l, rfl⟩ := (mem_lineGroup_iff hBN hac).mp hg
  have hl : l ≠ 0 := fun h => hg1 (by rw [h, zero_smul, lineElt_zero_right])
  have hind' : LinearIndependent K ![a, l • c] := by
    rw [LinearIndependent.pair_iff] at hind ⊢
    intro s t hst
    obtain ⟨h1, h2⟩ := hind s (t * l) (by rw [← hst, mul_smul])
    exact ⟨h1, (mul_eq_zero.mp h2).resolve_right hl⟩
  exact hs.siegel a (l • c) (by rw [map_smul, hac, smul_zero]) hind'

theorem I4Setting.isSiegelFamily_planeFamily (hs : I4Setting hBN Qf ρ) {π : Submodule K N}
    (hπ : IsPlane BN π) : IsSiegelFamily Qf (planeFamily hBN ρ π) where
  comm := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_mem_planeGroup hBN hπ.1 hg hh]
  card := by
    rw [planeFamily, Subgroup.card_map_of_injective hs.inj,
      card_planeGroup_of_isPlane hBN hs.nondegN hπ]
  siegel := by
    rintro _ ⟨g, hg, rfl⟩ hs1
    exact hs.isLongRootElement_map_of_isPlane hπ hg fun h => hs1 (by rw [h, map_one])

theorem planeFamily_map (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (g : Gsp BN)
    (σ : Submodule K N) :
    planeFamily hBN ρ (σ.map g.lin) = conjSubgroup (ρ g) (planeFamily hBN ρ σ) := by
  unfold planeFamily conjSubgroup
  rw [← map_planeGroup_conj hBN g σ, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply]

theorem conc_all_or_copl_all (hs : I4Setting hBN Qf ρ) :
    (∀ π, IsPlane BN π → Conc (planeFamily hBN ρ π)) ∨
      (∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π)) := by
  have hdich : ∀ π, IsPlane BN π →
      Conc (planeFamily hBN ρ π) ∨ Copl (planeFamily hBN ρ π) := fun π hπ =>
    (hs.isSiegelFamily_planeFamily hπ).conc_or_copl hs.nondeg
  have hiff : ∀ π π', IsPlane BN π → IsPlane BN π' →
      (Conc (planeFamily hBN ρ π) ↔ Conc (planeFamily hBN ρ π')) := by
    intro π π' hπ hπ'
    obtain ⟨g, rfl⟩ := exists_gsp_map_eq_of_isPlane hBN hs.nondegN hπ hπ'
    rw [planeFamily_map, conc_conjSubgroup_iff]
  by_cases h : ∃ π, IsPlane BN π ∧ Conc (planeFamily hBN ρ π)
  · obtain ⟨π₀, hπ₀, hc⟩ := h
    exact Or.inl fun π hπ => (hiff π₀ π hπ₀ hπ).mp hc
  · push Not at h
    exact Or.inr fun π hπ => (hdich π hπ).resolve_left (h π hπ)

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
