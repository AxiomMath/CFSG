module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {K : Type} [Field K] {r : ℕ}

theorem exists_plusFlagStab_of_borel_le [Finite K] (hr : 4 ≤ r)
    {K₀ : Subgroup ↥(orthElementaryGroup (quadPlus r K))}
    (hB : borel r K ≤ K₀.map (orthElementaryGroup (quadPlus r K)).subtype) :
    ∃ (e : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥(orthElementaryGroup (quadPlus r K)))
      (D : Finset ℕ), (∀ d ∈ D, 1 ≤ d ∧ d ≤ r) ∧ (r - 1 ∈ D → r ∈ D) ∧
      (K₀.map e.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype =
        plusFlagStab K r D := by
  have hr3 : 3 ≤ r := by omega
  set M₀ := K₀.map (orthElementaryGroup (quadPlus r K)).subtype with hM₀
  have hM₀E : M₀ ≤ orthElementaryGroup (quadPlus r K) := Subgroup.map_subtype_le _
  by_cases htw : weylElt r K ⟨r - 2, by omega⟩ ∉ M₀ ∧ weylElt r K ⟨r - 1, by omega⟩ ∈ M₀
  ·
    set e := plusGraphConj K (by omega : 1 ≤ r) with he
    set M := (K₀.map e.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype with hM
    have hmemM : ∀ g, g ∈ M ↔ swapPair K (⟨r - 1, by omega⟩ : Fin r) * g *
        swapPair K ⟨r - 1, by omega⟩ ∈ M₀ := by
      intro g
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
          swapPair K _ * ((e z : ↥(orthElementaryGroup (quadPlus r K))) :
            (Fin r ⊕ Fin r → K) ≃ₗ[K] _) * swapPair K _
        rw [he, coe_plusGraphConj]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
      · rintro ⟨z, hz, hzg⟩
        refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
        change ((e z : ↥(orthElementaryGroup (quadPlus r K))) :
          (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = g
        change (z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
          swapPair K _ * g * swapPair K _ at hzg
        rw [he, coe_plusGraphConj, hzg]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
    have hBM : borel r K ≤ M := fun b hb => (hmemM b).2 (hB (conj_swapPair_mem_borel hr3 hb))
    have hME : M ≤ orthElementaryGroup (quadPlus r K) := Subgroup.map_subtype_le _
    have hM₀X : ∀ h ∈ M₀, h • Xstar r K (by omega) = Xstar r K (by omega) := by
      intro h hh
      rw [eq_plusNodeStab_of_borel_le hr3 hM₀E hB] at hh
      have := (mem_plusNodeStab.1 hh).2 ⟨r - 2, by omega⟩ htw.1
      simpa [plusNodeSpace, show ¬ r - 2 + 1 ≤ r - 2 by omega] using this
    have hnM : weylElt r K ⟨r - 1, by omega⟩ ∉ M := by
      intro hn
      have h := hM₀X _ ((hmemM _).1 hn)
      have hσ := swapPair_smul_flag_top (K := K) hr3
      rw [mul_smul, mul_smul, hσ.2, ← hσ.1] at h
      apply (weylElt_last_smul (K := K) hr3).1
      have h2 := congrArg (swapPair K (⟨r - 1, by omega⟩ : Fin r) • ·) h
      simpa only [smul_smul, ← mul_assoc, swapPair_mul_self, one_mul, one_smul] using h2
    have hI : (⟨r - 2, by omega⟩ : Fin r) ∈ {i | weylElt r K i ∉ M} →
        (⟨r - 1, by omega⟩ : Fin r) ∈ {i | weylElt r K i ∉ M} := fun _ => hnM
    refine ⟨e, plusNodeDims {i | weylElt r K i ∉ M}, (plusNodeDims_props hr3 hI).1,
      (plusNodeDims_props hr3 hI).2, ?_⟩
    rw [← plusNodeStab_eq_plusFlagStab hr3 hI]
    exact eq_plusNodeStab_of_borel_le hr3 hME hBM
  · have hI : (⟨r - 2, by omega⟩ : Fin r) ∈ {i | weylElt r K i ∉ M₀} →
        (⟨r - 1, by omega⟩ : Fin r) ∈ {i | weylElt r K i ∉ M₀} := fun h2 => by
      by_contra h1
      exact htw ⟨h2, not_not.1 h1⟩
    refine ⟨MulEquiv.refl _, plusNodeDims {i | weylElt r K i ∉ M₀},
      (plusNodeDims_props hr3 hI).1, (plusNodeDims_props hr3 hI).2, ?_⟩
    have hid : K₀.map (MulEquiv.refl ↥(orthElementaryGroup (quadPlus r K))).toMonoidHom = K₀ := by
      ext x
      simp
    rw [hid, ← plusNodeStab_eq_plusFlagStab hr3 hI]
    exact eq_plusNodeStab_of_borel_le hr3 hM₀E hB

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
