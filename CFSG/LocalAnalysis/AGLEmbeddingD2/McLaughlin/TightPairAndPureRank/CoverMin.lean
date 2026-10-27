module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_minOver_of_node
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (i : Fin D.rank) :
    ∃ P : Subgroup K, borel D H ≤ P ∧ rankOne D.rootGroup i ≤ P ∧ P ≠ borel D H ∧
      ∀ Q : Subgroup K, borel D H ≤ Q → Q ≤ P → Q = borel D H ∨ Q = P := by
  haveI := cartan_borel_weylN_normal hct hext
  have hBN := isBNPair_borel_weylN hct hext
  set B := borel D H with hB
  set N := weylN n H with hN
  set s : WeylGroup B N := ((⟨n i, n_mem_weylN i⟩ : N) : WeylGroup B N) with hs
  have hsS : s ∈ simpleRefl D n H := ⟨i, rfl⟩
  have hJS : ({s} : Set (WeylGroup B N)) ⊆ simpleRefl D n H := Set.singleton_subset_iff.2 hsS
  have hemptyS : (∅ : Set (WeylGroup B N)) ⊆ simpleRefl D n H := Set.empty_subset _
  have hP0 : parabolic B N (∅ : Set (WeylGroup B N)) = B := by
    ext x
    rw [hBN.mem_parabolic_iff hemptyS]
    constructor
    · rintro ⟨w, hw, hx⟩
      rw [Subgroup.closure_empty, Subgroup.mem_bot] at hw
      rw [hw, mem_dc_one] at hx
      exact hx
    · intro hx
      exact ⟨1, one_mem _, mem_dc_one.2 hx⟩
  refine ⟨parabolic B N {s}, hBN.le_parabolic hJS, ?_, ?_, ?_⟩
  ·
    have hnP : n i ∈ parabolic B N {s} := by
      rw [hBN.mem_parabolic_iff hJS]
      exact ⟨s, Subgroup.subset_closure rfl,
        mem_dc_mk_iff.2 ⟨1, one_mem _, 1, one_mem _, by simp [hB]⟩⟩
    intro g hg
    rcases hext.rankOne_bruhat i g hg with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
      exact mul_mem (hBN.le_parabolic hJS (iSup_le_borel (le_iSup H i hh)))
        (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hu))
    · have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
      exact mul_mem (mul_mem (mul_mem
        (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hu)) hnP)
        (hBN.le_parabolic hJS (iSup_le_borel (le_iSup H i hh))))
        (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hv))
  · intro heq
    have : ({s} : Set (WeylGroup B N)) = ∅ :=
      hBN.parabolic_injOn hJS hemptyS (heq.trans hP0.symm)
    exact Set.singleton_ne_empty s this
  · intro Q hBQ hQP
    obtain ⟨J, ⟨hJ, hQJ⟩, -⟩ := hBN.existsUnique_parabolic hBQ
    have hJs : J ⊆ {s} := (hBN.parabolic_le_iff hJ hJS).1 (hQJ ▸ hQP)
    rcases Set.subset_singleton_iff_eq.1 hJs with h0 | h1
    · left
      rw [hQJ, h0, hP0]
    · right
      rw [hQJ, h1]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
