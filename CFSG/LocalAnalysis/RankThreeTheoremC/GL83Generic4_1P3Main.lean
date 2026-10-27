module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Cyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3NoBM

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped MatrixGroups
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem isPrimeThreeType_of_isRankTwoSEGroup {Q : Type} [Group Q] (h : IsRankTwoSEGroup 3 Q) :
    IsPrimeThreeType Q := by
  rcases h with ⟨_, f⟩ | ⟨q, hq1, hq2, hl⟩ | ⟨h5, _⟩ | ⟨_, h⟩ | ⟨h5, _⟩ | ⟨h11, _⟩
  · exact Or.inl f
  · exact Or.inr (Or.inl ⟨q, hq1, hq2, hl⟩)
  · exact absurd h5 (by norm_num)
  · rcases h with ⟨q, hq1, hq2, hl⟩ | f
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq1, hq2, hl⟩)))
    · exact Or.inr (Or.inr (Or.inl f))
  · exact absurd h5 (by norm_num)
  · exact absurd h11 (by norm_num)

theorem isPrimeThreeType_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsPrimeThreeType Q') : IsPrimeThreeType Q := by
  rcases h with f | ⟨q, hq1, hq2, hl⟩ | f | ⟨q, hq1, hq2, hl⟩ | hl
  · exact Or.inl ⟨e.trans f.some⟩
  · exact Or.inr (Or.inl ⟨q, hq1, hq2, isoLie_of_mulEquiv e.symm hl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f.some⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq1, hq2, isoLie_of_mulEquiv e.symm hl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isoLie_of_mulEquiv e.symm hl))))

theorem genericPrimeThree_of_types {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hU0 : FullCoreLocal G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic)
    (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (R : GL83GenericPrimeThreeTypes G) : GL83GenericPrimeThree G := by
  intro p hp P M hM hfail hIH x hgen hp3
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S, hSmap, hsh⟩ := exists_genericShadow3 hS hU0 hp hp3 hM hgen
  have hBM : ∀ L : Subgroup (GenericReduced p x), IsComponentOf L ⊤ → NotBM ↥L :=
    fun L hL => notBM_of_notSecExcl3
      (notSecExcl3_of_noExcludedSection3 hno hL.2.2 (hsh.center_eq_bot K4 hL))
  obtain ⟨Lb, hLbc, hLbn, huniq, hLbZ, hLbΓ, hLblist⟩ := hsh.exists_main3_noBM K4 K1 K2 K3 hBM
  obtain ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ := id hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have : Lb.Normal := hLbn
  have hLbperf : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp ⟨hLbc.2.2.1⟩
  obtain ⟨hLsimple, -, -⟩ := hsh.simple_nonab_catalog K4 hLbc
  have hLb_ne : Lb ≠ ⊥ := by
    intro h
    have := hLsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Lb).mp this h
  set J : Subgroup C := perfectCore (Lb.comap π) with hJ
  have hJn : J.Normal := normal_perfectCore _
  have hJperf : ⁅J, J⁆ = J := commutator_perfectCore _
  have hJmap : J.map π = Lb :=
    map_perfectCore_comap π (QuotientGroup.mk'_surjective O) Lb hLbperf
  set JG : Subgroup G := J.map C.subtype with hJG
  have hJGC : JG ≤ C := Subgroup.map_subtype_le J
  have hCJG : C ≤ normalizer (JG : Set G) := le_normalizer_map_subtype J
  have hJGperf : ⁅JG, JG⁆ = JG := commutator_map_subtype J hJperf
  have hsimple : IsSimpleGroup ↥(J.map π) := by rw [hJmap]; exact hLsimple
  have hnot : ¬ JG ≤ M := by
    intro hle
    apply hLbΓ
    have hJ' : J ≤ (C ⊓ M).subgroupOf C := fun j hj =>
      Subgroup.mem_subgroupOf.mpr ⟨j.2, hle ⟨j, hj, rfl⟩⟩
    rw [← hJmap]
    exact Subgroup.map_mono hJ'
  have hlt : rankThreePrimeCore p JG < JG :=
    rankThreePrimeCore_map_subtype_lt J (by rw [hJmap]; exact hLb_ne)
  obtain ⟨ψ, hψ, hψker⟩ := exists_surjective_ker_primeCore (p := p) (C := C) J
  have hlist : IsPrimeThreeType ↥(J.map π) := by
    subst hp3
    rcases hLblist with h | h
    · exact isPrimeThreeType_of_mulEquiv (MulEquiv.subgroupCongr hJmap)
        (isPrimeThreeType_of_isRankTwoSEGroup h)
    · exact isPrimeThreeType_of_mulEquiv (MulEquiv.subgroupCongr hJmap)
        (Or.inr (Or.inr (Or.inr (Or.inr h))))
  exact R p hp P M hM hfail hIH x ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ hp3 JG hJGC hCJG
    (Subgroup.isPerfect_iff.mpr hJGperf) hlt
    (fun N hN hn hON => eq_or_eq_of_normal J hsimple N hN hn hON) hnot (↥(J.map π)) ψ hψ hψker
    hlist

end CFSG.LocalAnalysis.RankThreeTheoremC
