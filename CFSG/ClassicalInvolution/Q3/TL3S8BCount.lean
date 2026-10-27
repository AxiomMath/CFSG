module

public import CFSG.ClassicalInvolution.Q3.TL3S8BE2
public import CFSG.ClassicalInvolution.Q3.TL3S8BAut

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem TightE2Prime.exists_two_generators_inf_cStar {K : Subgroup G} {S : Sylow 2 G}
    (hE : TightE2Prime K S) {P : Subgroup G} (hPS : P ≤ (S : Subgroup G)) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = P ⊓ cStar K := by
  classical
  obtain ⟨C, hCcyc, hCT, hidx⟩ := hE
  set D : Subgroup G := P ⊓ cStar K with hD
  have hDT : D ≤ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := fun x hx =>
    ⟨hPS hx.1, mem_centralizer_inf_of_mem_cStar S.isPGroup' hx.2 (hPS hx.1)⟩
  have hDC : IsCyclic ↥(D ⊓ C) := Subgroup.isCyclic_of_le (H' := C) inf_le_right
  obtain ⟨⟨c, hc⟩, hcgen⟩ := hDC.exists_generator
  have hCz : D ⊓ C = Subgroup.zpowers c := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcgen ⟨y, hy⟩)
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.mpr hc
  by_cases hDt : D ≤ C
  · refine ⟨{c}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, ← hCz, inf_eq_left.mpr hDt]
  · obtain ⟨x, hxD, hxC⟩ := Set.not_subset.mp hDt
    refine ⟨{c, x}, Finset.card_le_two, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hc.1
      · exact hxD
    · intro y hyD
      have hcl : Subgroup.zpowers c ≤ Subgroup.closure (({c, x} : Finset G) : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      have hxcl : x ∈ Subgroup.closure (({c, x} : Finset G) : Set G) :=
        Subgroup.subset_closure (by simp)
      by_cases hyC : y ∈ C
      · exact hcl (hCz ▸ ⟨hyD, hyC⟩)
      · have hmem : x⁻¹ * y ∈ D ⊓ C :=
          ⟨D.mul_mem (D.inv_mem hxD) hyD, hidx x (hDT hxD) y (hDT hyD) hxC hyC⟩
        rw [show y = x * (x⁻¹ * y) by group]
        exact Subgroup.mul_mem _ hxcl (hcl (hCz ▸ hmem))

theorem twoSubgroupsFourGenerated_of_tightE2Prime {K : Subgroup G} {S : Sylow 2 G}
    (hE : TightE2Prime K S) (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G))
    (hE3 : NormalizerQuotientTwoGeneratedStar K) : TwoSubgroupsFourGenerated G := by
  classical
  refine fourGenerated_of_sylow S fun P hPS => ?_
  obtain ⟨s₁, hs₁, hcl₁⟩ := hE3 P (S.isPGroup'.to_le hPS) (hPS.trans hSN)
  obtain ⟨s₂, hs₂, hcl₂⟩ := hE.exists_two_generators_inf_cStar hPS
  refine ⟨s₁ ∪ s₂, (Finset.card_union_le _ _).trans (by omega), ?_⟩
  rw [Finset.coe_union, Subgroup.closure_union, hcl₂, hcl₁]

omit [Finite G] in
theorem twoSubgroupsFourGenerated_subgroup (F : Subgroup G) (h : TwoSubgroupsFourGenerated G) :
    TwoSubgroupsFourGenerated F := by
  classical
  intro P hP
  obtain ⟨s, hs4, hsP⟩ := h (P.map F.subtype) (hP.map _)
  have hsF : ∀ x ∈ s, x ∈ F := fun x hx => by
    have : x ∈ Subgroup.closure (s : Set G) := Subgroup.subset_closure hx
    rw [hsP] at this
    exact Subgroup.map_subtype_le _ this
  have hcard : (s.subtype (· ∈ F)).card ≤ s.card := by
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  refine ⟨s.subtype (· ∈ F), hcard.trans hs4, ?_⟩
  · apply Subgroup.map_injective F.subtype_injective
    have himg : F.subtype '' ((s.subtype (· ∈ F) : Finset F) : Set F) = (s : Set G) := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hsF x hx⟩, hx, rfl⟩
    rw [MonoidHom.map_closure, himg, hsP]

namespace TightSylowStd

variable {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}

theorem twoSubgroupsFourGenerated_of_e2Prime (h : TightSylowStd R S t T)
    (hE : TightE2Prime (tightCore R) T) : TwoSubgroupsFourGenerated (genFittingFStar G) :=
  twoSubgroupsFourGenerated_subgroup _
    (twoSubgroupsFourGenerated_of_tightE2Prime hE h.hTN h.normalizerQuotientTwoGeneratedStar_core)

end TightSylowStd

end CFSG.ClassicalInvolution.Q3
