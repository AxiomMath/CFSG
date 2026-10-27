module

public import CFSG.ClassicalInvolution.RouteD.TypeACount

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem centralizingMembers_eq_insert [Finite G] {Ω : Set (Subgroup G)} {x : G} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) {𝓡 : Set (Subgroup G)}
    (h𝓡 : 𝓡 ⊆ centralizingMembers Ω {x}) (hNR : N ∉ 𝓡)
    (hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard) :
    centralizingMembers Ω {x} = insert N 𝓡 := by
  refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset hN h𝓡) ?_ (Set.toFinite _)).symm
  rw [Set.ncard_insert_of_notMem hNR (Set.toFinite _)]
  omega

theorem not_commutes_self_of_isClassicalMember {L : Subgroup G} {z : G}
    (h : IsClassicalMember p f L z) : ¬ Commutes L L := by
  intro hc
  have h1 : ⁅L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun c hc' => hc c hc' a ha
  have h2 := commutator_eq_of_isClassicalMember h
  rw [h1] at h2
  have hz : z ∈ L := h.mem
  rw [← h2, Subgroup.mem_bot] at hz
  have := h.orderOf_eq_two
  rw [hz, orderOf_one] at this
  omega

theorem injective_comp_tailBlock {F : Type} [Field F] {k : ℕ} {H : Type} [Group H]
    {ψ : SL(k + 2, F) →* H} (hker : ψ.ker ≤ Subgroup.center SL(k + 2, F)) :
    Function.Injective (ψ.comp (tailBlock F k)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  exact tailBlock_eq_one_of_mem_center (hker (MonoidHom.mem_ker.mpr hs))

theorem typeA_centralizingMembers [Finite G] {m : ℕ} (hm : 1 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeA p f m Ω z) (hP1 : LocalOddCentral Ω {z})
    (h2 : (2 : GaloisField p f) ≠ 0) {ψ : SL(m + 1 + 2, GaloisField p f) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField p f))
    (hΩψ : ∀ R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω)
    {g₀ : G} (hg₀ : (rootSL2 (GaloisField p f) (by omega : 2 ≤ m + 1 + 2)).map ψ = conjSub g₀ K) :
    centralizingMembers Ω {g₀ * z * g₀⁻¹} =
      insert ((rootSL2 (GaloisField p f) (by omega : 2 ≤ m + 1 + 2)).map ψ)
        ((fun R => R.map (ψ.comp (tailBlock (GaloisField p f) (m + 1)))) ''
          longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1)) := by
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  set F := GaloisField p f with hF
  set N := (rootSL2 F hn).map ψ with hNdef
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hNm : N ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hxN : g₀ * z * g₀⁻¹ ∈ N := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  have hmemΩ : ∀ R ∈ longRootSet (K := F) hk, R.map (ψ.comp (tailBlock F (m + 1))) ∈ Ω := by
    intro R hR
    have := hΩψ _ (map_tailBlock_mem_longRootSet h2 hk hR)
    rwa [Subgroup.map_map] at this
  have hcomm : ∀ R ∈ longRootSet (K := F) hk,
      Commutes (R.map (ψ.comp (tailBlock F (m + 1)))) N := by
    rintro R hR _ ⟨s, hs, rfl⟩ _ ⟨_, ⟨r, rfl⟩, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg ψ (tailBlock_commutes_rootSL2 hn s r)
  have h𝓡 : (fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk ⊆
      centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨hmemΩ R hR, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm R hR y hy _ hxN
  have hNR : N ∉ (fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk := by
    rintro ⟨R, hR, hRN⟩
    have h1 := hcomm R hR
    have hRN' : R.map (ψ.comp (tailBlock F (m + 1))) = N := hRN
    rw [hRN'] at h1
    have h2' : Commutes K K := by
      rw [hg₀] at h1
      exact (commutes_conjSub_iff g₀).mp h1
    exact not_commutes_self_of_isClassicalMember hz h2'
  have hinj : Function.Injective
      (fun R : Subgroup SL(m + 1, F) => R.map (ψ.comp (tailBlock F (m + 1)))) :=
    Subgroup.map_injective (injective_comp_tailBlock hker)
  have hcard : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤
      1 + ((fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk).ncard := by
    rw [Set.ncard_image_of_injective _ hinj, ncard_centralizingMembers_conj hΩ.conjInvariant,
      ncard_centralizingMembers_eq hΩ hP1]
    exact hshape.ncard_locFamily_le hm
  exact centralizingMembers_eq_insert hNm h𝓡 hNR hcard

end CFSG.ClassicalInvolution.RouteD
