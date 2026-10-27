module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainData
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets4
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.ClassicalInvolution.Q3.Q3T6AutUni

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups

section Steps


variable {G : Type} [Group G] [Finite G]

theorem eq_conjClass3 {Ω : Set (Subgroup G)} {K : Subgroup G} (hs : AscStand3 Ω K) :
    Ω = CoreAssembly.conjClass K := by
  ext J
  constructor
  · intro hJ
    obtain ⟨g, hg⟩ := hs.trans J hJ
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact hs.hyp.conjInvariant g K hs.mem

theorem exists_std6Three {Ω : Set (Subgroup G)} {K : Subgroup G} (hs : AscStand3 Ω K)
    (he : DEdgeless Ω) (hc : ¬ ConcOrTF4 G) (h3 : 3 ≤ CFSG.Open.twoRank G) :
    ∃ (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6Three Ω K S R z := by
  obtain ⟨z, hz⟩ := hs.hyp.classical K hs.mem
  have hU : IsUniqueInvolution K z := hz.isUniqueInvolution (MemberType.cert_sl2 3 1)
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  set R : Subgroup G := Subgroup.map K.subtype (P : Subgroup ↥K) with hR
  have hRp : IsPGroup 2 R := P.isPGroup'.map K.subtype
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  exact ⟨S, R, z, ⟨hs, he, hU, ⟨K, hs.mem, P, rfl⟩, Subgroup.map_subtype_le _, hRS, hc, h3⟩⟩

theorem w69Three :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
      AscStand3 Ω K → ∀ S : Sylow 2 G, ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) := by
  intro G _ _ _ Ω K hs S
  have hΩ : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

theorem exists_two_generators_inf_cStar3 [IsSimpleGroup G] (hE : C19_E2Prime3) {K : Subgroup G}
    {z : G} {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W) {P : Subgroup G}
    (hPS : P ≤ (S : Subgroup G)) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = P ⊓ cStar K := by
  classical
  obtain ⟨C, hCcyc, hCT, hidx⟩ := hE G K z S W hd
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

theorem twoSubgroupsFourGenerated_of_e2Prime3 [IsSimpleGroup G] (hE : C19_E2Prime3)
    {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W)
    (hE3 : NormalizerQuotientTwoGeneratedStar K) : TwoSubgroupsFourGenerated G := by
  classical
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [hd.tight.normEq]
    exact hd.hSz
  refine fourGenerated_of_sylow S fun P hPS => ?_
  obtain ⟨s₁, hs₁, hcl₁⟩ := hE3 P (S.isPGroup'.to_le hPS) (hPS.trans hSN)
  obtain ⟨s₂, hs₂, hcl₂⟩ := exists_two_generators_inf_cStar3 hE hd hPS
  refine ⟨s₁ ∪ s₂, (Finset.card_union_le _ _).trans (by omega), ?_⟩
  rw [Finset.coe_union, Subgroup.closure_union, hcl₂, hcl₁]

theorem thm6A3_of_steps (h2 : C19_2Three) (h4 : C19_4Three)
    (hmain : C19_mainThree) : Thm6A3 := by
  have hW := CFSG.ClassicalInvolution.Q3.Q3T6.w69Three
  intro G _ _ _ Ω K hs h3 hn he
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD hn
  obtain ⟨S, R, z, hstd⟩ := exists_std6Three hs he hc h3
  obtain ⟨W, hWmem, hWS⟩ := hW G Ω K hs S
  rcases h2 G Ω K hs he W hWmem with hZ | hS3
  · exact absurd (h4 G Ω K S R z hstd W hWmem hWS hZ) hc
  · exact absurd (hmain G Ω K S R z hstd W hWmem hWS hS3) hc

end Steps

section Assembly


structure Thm6Layer3 : Prop where
  data : DataOfStd6Three
  mu : C19_2Three
  sd : C19_4Three
  e2 : C19_11b3 → C19_E2Prime3

theorem c19_main3_of (hdata : DataOfStd6Three) (he2 : C19_11b3 → C19_E2Prime3)
    (h : C19_11b3) : C19_mainThree := by
  intro G _ _ _ Ω K S R z hstd W hW hWS hS3
  have hd := hdata G Ω K S R z hstd W hW hWS hS3
  have hE3 := normalizerQuotientTwoGeneratedStar_of_memberU hd.tight.member
  exact Or.inr (twoSubgroupsFourGenerated_of_e2Prime3 (he2 h) hd hE3)

theorem thm6A3_of_c19_11b3 (L : Thm6Layer3) (h : C19_11b3) : Thm6A3 :=
  thm6A3_of_steps L.mu L.sd (c19_main3_of L.data L.e2 h)

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T6
