module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscInv
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscComp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscQuasi

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ProperTwoGeneratedCore CFSG.ComponentClassification.FooteLit

variable {X : Type} [Group X] [Finite X]

theorem pRank_centralizer_eq_one {L : Subgroup X} {u : X} (huZ : u ∈ center X)
    (hu : orderOf u = 2) (h : Open.pRank 2 (centralizer (L : Set X)) ≤ 1) :
    CFSG.pRank 2 ↥(centralizer (L : Set X)) = 1 := by
  rw [SectionRank.pRank_eq_open_pRank_top,
    ← RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 one_lt_two]
  refine le_antisymm h ((Lemma37.CyclicCase.one_le_pRank_closure_of_orderOf_eq_two hu).trans
    (SectionRank.pRank_mono one_lt_two ?_))
  rw [closure_le, Set.singleton_subset_iff]
  exact mem_centralizer_iff.mpr fun l _ => mem_center_iff.mp huZ l

theorem aschbacherCentralCoreInput_holds :
    AschbacherCentralCoreInput := by
  intro B _ _ S hcore t ht htZ hrank hcl hA9
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3B : 3 ≤ Open.twoRank B := by
    rwa [SectionRank.pRank_eq_open_pRank_top] at hrank
  obtain ⟨-, -, hlt, -, h3, hodd, huZ, hu, huO, hrk, -, hlay⟩ :=
    central_involution_proper_core_local_structure h3B t htZ ht S hcore
  set P := S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 B)) with hP
  have hPY : (P : Subgroup (B ⧸ pPrimeCore 2 B)) ≤
      Open.properTwoGenCoreGamma (P : Subgroup (B ⧸ pPrimeCore 2 B)) 2 :=
    sylow_le_gamma P (by rw [sylow_two_rank_eq]; omega)
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (B ⧸ pPrimeCore 2 B), CFSG.IsComponent L := by
    by_contra hno
    push Not at hno
    apply hlay
    simp only [CFSG.layer.eq_sSup]
    exact sSup_eq_bot.mpr fun K hK => absurd hK (hno K)
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  right
  by_cases huL : QuotientGroup.mk' (pPrimeCore 2 B) t ∈ L
  ·
    obtain ⟨K, hK, hKmap, htK⟩ := exists_isPComponent_mem hL ht2 huL
    have hL2 : 2 ≤ Open.pRank 2 L := by
      by_contra hlt2
      apply hcl K hK htK
      rw [pRank_eq_pRank_map hK, hKmap, SectionRank.pRank_eq_open_pRank_top,
        ← RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 one_lt_two]
      omega
    obtain ⟨hLn, hCL, hperf, hZ, he⟩ :=
      component_quasi_of_mem hodd huZ hu huO hrk P hlt.ne hPY le_rfl hL huL hL2
    rcases he with he | he
    · exfalso
      obtain ⟨e⟩ := he
      obtain ⟨eK⟩ := nonempty_quotientEquivMap hK
      exact hA9 K hK htK (IsCoverOverTwo.of_mulEquiv (eK.trans (MulEquiv.subgroupCongr hKmap))
        (isCoverOverTwo_of_card_center hperf hZ e))
    · obtain ⟨e⟩ := he
      refine ⟨L, hLn, Or.inr (Or.inl (isCoverOverTwo_of_card_center hperf hZ e)),
        pRank_centralizer_eq_one huZ hu hCL, fun x hx => ?_⟩
      have hx2 := pow_orderOf_eq_one x
      rw [hx, pow_two] at hx2
      exact mem_sup_centralizer_of_odd_outer hperf (CGT.T75M.sz_outer_odd le_rfl e) hx2
  ·
    obtain ⟨hLn, hBen, hCL, hinv⟩ :=
      component_bender_of_not_mem hodd huZ hu huO hrk h3 P hlt.ne hPY le_rfl hL huL
    exact ⟨L, hLn, Or.inl hBen, pRank_centralizer_eq_one huZ hu hCL, hinv⟩

end CFSG.ComponentClassification.Foote5
