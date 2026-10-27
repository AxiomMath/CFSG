module

public import CFSG.ClassicalInvolution.AschTight.S1911E2a

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem exists_two_generators_inf_cStar (hE : C19_E2PrimeTmp p f)
    (hd : Sec19Data p f K z S W) {P : Subgroup G} (hPS : P ≤ (S : Subgroup G)) :
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

theorem twoSubgroupsFourGenerated_of_e2Prime (hE : C19_E2PrimeTmp p f)
    (hd : Sec19Data p f K z S W) (hE3 : NormalizerQuotientTwoGeneratedStar K) :
    TwoSubgroupsFourGenerated G := by
  classical
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact hd.hSz
  refine fourGenerated_of_sylow S fun P hPS => ?_
  obtain ⟨s₁, hs₁, hcl₁⟩ := hE3 P (S.isPGroup'.to_le hPS) (hPS.trans hSN)
  obtain ⟨s₂, hs₂, hcl₂⟩ := exists_two_generators_inf_cStar hE hd hPS
  refine ⟨s₁ ∪ s₂, (Finset.card_union_le _ _).trans (by omega), ?_⟩
  rw [Finset.coe_union, Subgroup.closure_union, hcl₂, hcl₁]

variable (p f) in
theorem tightControlledD_of_targets4 (hB3 : GoldschmidtB3Tmp) (h11b : C19_11bTmp p f)
    (h16 : C19_16STmp p f) (hIH : IHAllD p f) : TightControlledD p f := by
  intro G _ _ _ K z ht0
  have ht := S19R.tightStd_of_tightBranchD ht0
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD ht.branch.notFourGenerated
  exfalso
  by_cases hA : AllTypeTwo K z
  · exact false_of_allTypeTwo hB3 ht hA
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  obtain ⟨W, hWmem, hWS⟩ := exists_wSet_le ht S
  have hd : Sec19Data p f K z S W :=
    ⟨ht, hA, hIH G K z ht.branch, hc, ⟨Q₀, hRS⟩, hSz, hWmem, hWS⟩
  have hE3 := normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo ht.branch.odd
    ht.branch.five ht.branch.member (innerDiagonalTwo_of_sec19 h16 hd)
  exact ht.branch.notFourGenerated
    (twoSubgroupsFourGenerated_of_e2Prime (c19_E2PrimeTmp_of p f h11b) hd hE3)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
