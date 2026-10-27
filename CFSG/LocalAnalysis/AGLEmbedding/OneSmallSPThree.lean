module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallAlphaThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace ReducedNongeneration

variable {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {X₀ : Subgroup X}

theorem false_of_outTwo_of_exp (h : ReducedNongeneration 3 X R X₀)
    (hR4 : 4 ≤ Open.pRank 3 (R : Subgroup X)) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = 3) {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hzK : z ∈ K) (hout : KOutTwoGroup K)
    (hexp : ∀ t ∈ (R : Subgroup X) ⊓ K, t ^ 3 = 1)
    (hrank : Open.pRank 3 ((R : Subgroup X) ⊓ K) ≤ 3) : False := by
  have hp := h.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hdec : ∀ r ∈ (R : Subgroup X), ∃ t ∈ (R : Subgroup X) ⊓ K,
      ∃ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), t * c = r :=
    fun r hr => exists_mul_eq_of_kOutTwoGroup hp h.ne_two R hout hr
  have hC := h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK
  have hzR : z ∈ (R : Subgroup X) := mem_sylow_of_mem_center hz hzp R
  obtain ⟨E, hER, hE, hEcard⟩ := pRank_attained 3 hp (R : Subgroup X)
  have hET : E ≤ (R : Subgroup X) ⊓ K := fun e he =>
    mem_inf_of_pow_eq_one_of_decomp hp hzR hzK hC hdec hexp (hER he) (hE.2 e he)
  have hle : Open.pRank 3 (R : Subgroup X) ≤ Open.pRank 3 ((R : Subgroup X) ⊓ K) :=
    le_csSup (pRank_bddAbove 3 hp _) ⟨E, hET, hE, hEcard⟩
  omega

theorem j3_of_alphaThree_of_mem (h : ReducedNongeneration 3 X R X₀)
    (hR4 : 4 ≤ Open.pRank 3 (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hα : KFactAlphaW)
    (hK3 : KFactAlphaThreeWeak) :
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) := by
  have hp := h.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hcat := hX.isCatalogGroup_center_quotient hK
  have hZ1 := center_ne_bot_of_mem hp hz hzp hzK
  have hZp := isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  have hZc := h.isCyclic_center hK hKn
  have hweak : GLBWeakCore 3 (T : Subgroup K) = ⊤ → 3 ≤ Open.pRank 3 (⊤ : Subgroup K) → False :=
    fun hc h3 => h.false_of_three_le_pRank_of_le hKn (le_of_weakCore_eq_top h T hT hc) h3
  rcases hα K hK.2.2 hcat 3 hp h.ne_two hZ1 hZp hZc T with
    ⟨hgen, h3 | hout⟩ | ⟨hgen, hZ3, hout⟩ | hb | ⟨hc, h3⟩ | ⟨hout, he1 | hexp | he3⟩
  · exact (h.false_of_three_le_pRank_of_le hKn (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      h3).elim
  · exact (h.false_of_kOutNormalSylow (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout).elim
  · exact (h.false_of_kOutNormalSylow (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout).elim
  · exact (h.false_of_pRank_mulAut_le_two hR4 hz hzp hK hKn hzK hb).elim
  · exact (hweak hc h3).elim
  · rcases hK3 K hK.2.2 hcat hZ1 hZp hZc hout T (Or.inl he1) with ⟨hc, h3⟩ | hJ
    · exact (hweak hc h3).elim
    · exact hJ
  · obtain ⟨hexp', hrank'⟩ := pow_and_pRank_map hp hexp
    rw [hT] at hexp' hrank'
    exact (h.false_of_outTwo_of_exp hR4 hz hzp hK hKn hzK hout hexp' hrank').elim
  · rcases hK3 K hK.2.2 hcat hZ1 hZp hZc hout T (Or.inr he3) with ⟨hc, h3⟩ | hJ
    · exact (hweak hc h3).elim
    · exact hJ

end ReducedNongeneration

theorem stmtSmallSPInThree_of (hα : KFactAlphaW) (hK3 : KFactAlphaThreeWeak)
    (hJ3 : KFactJ3Involve) (hSch : KFactCatalogSchreier) : StmtSmallSPInThree := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hp3 hSP hin hA6
  subst hp3
  obtain ⟨P', Pbar, KC, -, -, -, hRC⟩ := hd.exists_reducedCentralizer hz hSP
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : d1CzElt 3 z ∈ KC := by
    by_contra hzK
    refine hin fun L hL => ?_
    rw [hRC.unique L hL]
    exact hzK
  have hJ := hRC.red.j3_of_alphaThree_of_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp
    hRC.normal hzK hα hK3
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_of_reducedCentralizer hz hRC hSch
  obtain ⟨T₁, -, hs₁, hn₁, hc₁, hT₁nc, hΓ₁, -⟩ := hd.exists_sylow
  exact hA6 ⟨hJ3 KC hJ K hs₁ hn₁ hc₁ T₁ hT₁nc hΓ₁ hd.small A f hf, KC, hRC.comp, hzK, hJ⟩

end CFSG.AGLEmbedding
