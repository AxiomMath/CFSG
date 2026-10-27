module

public import CFSG.ClassicalInvolution.Asc77.AscT7XGen
import CFSG.ClassicalInvolution.Asc77.AscT7HC4
import CFSG.ClassicalInvolution.Asc77.AscMuTabProved
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.Assembly.LowTwoRank

namespace T7X

section Combinatorics

variable {G : Type} [Group G]

theorem dEdgeless_of_trans_isolated {Φ : Set (Subgroup G)} (hΦ : ConjInvariant Φ)
    (htr : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : G, conjSub g K = L) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Φ)
    (hiso : ∀ M ∈ Φ, ¬ dAdj Φ K₀ M) : DEdgeless Φ := by
  intro A hA B hB hAB
  obtain ⟨g, hg⟩ := htr K₀ hK₀ A hA
  have h1 := T7A.dAdj_conjSub hΦ hAB g⁻¹
  rw [← hg, conjSub_inv_conjSub] at h1
  exact hiso (conjSub g⁻¹ B) (hΦ g⁻¹ B hB) h1

theorem top_notMem_of_trans {Φ : Set (Subgroup G)}
    (htr : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : G, conjSub g K = L) {A B : Subgroup G} (hA : A ∈ Φ)
    (hB : B ∈ Φ) (hAB : A ≠ B) : (⊤ : Subgroup G) ∉ Φ := by
  intro hT
  obtain ⟨g, hg⟩ := htr ⊤ hT A hA
  obtain ⟨g', hg'⟩ := htr ⊤ hT B hB
  rw [conjSub_top_eq_top] at hg hg'
  exact hAB (hg.symm.trans hg')

end Combinatorics

section Star

variable {G : Type} [Group G] [Finite G] {Λ : Set (Subgroup G)} {Y K J R U : Subgroup G}

theorem omegaStarNbr_subgroupOf_of_data (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Λ) (hne : J ≠ K)
    (hRJ : IsSylow2In R J) (hUR : U ≤ R) (hcyc : IsCyclic ↥U)
    (hcard : Nat.card ↥R = 2 * Nat.card ↥U) (hUN : U ≤ Subgroup.normalizer (K : Set G)) :
    J.subgroupOf Y ∈ omegaStarNbr (restrictFamily Λ Y) (K.subgroupOf Y) := by
  have hRY : R ≤ Y := hRJ.1.trans hJY
  have hUY : U ≤ Y := hUR.trans hRY
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrel' : (U.subgroupOf Y).relIndex (R.subgroupOf Y) = 2 := by
    have h2 := Subgroup.relIndex_map_map_of_injective (U.subgroupOf Y) (R.subgroupOf Y)
      Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUY, Subgroup.map_subgroupOf_eq_of_le hRY] at h2
    rw [← h2]
    exact hrel
  refine ⟨subgroupOf_mem_restrictFamily hJ hJY, subgroupOf_ne_of_ne hKY hJY hne, U.subgroupOf Y,
    ⟨R.subgroupOf Y, mem_RSet_restrict hJ hJY hRJ, Subgroup.subgroupOf_mono Y hUR, ?_, hrel'⟩,
    Subgroup.subgroupOf_mono Y (hUR.trans hRJ.1), ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUY)).mpr hcyc
  · intro u hu
    exact (mem_normalizer_subgroupOf_iff hKY).mp (hUN (Subgroup.mem_subgroupOf.mp hu))

end Star


section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {e : G}

 in
theorem layer_shape_of_data (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hn : CITBelowU p f (Nat.card G)) (he2 : e * e = 1)
    (hnc : ¬ ({e} : Set G) ⊆ Subgroup.center G) {K K' J : Subgroup G}
    (hperp : KPerp Ω K = {K, K'}) (hKt : K ∈ tqMembers Ω e) (hJt : J ∈ tqMembers Ω e)
    (hK't : K' ∉ tqMembers Ω e) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) (hzj : z * j = j * z) (hne : z ≠ j) {R U : Subgroup G}
    (hRJ : IsSylow2In R J) (hRe : R ≤ Subgroup.centralizer ({e} : Set G)) (hUR : U ≤ R)
    (hcyc : IsCyclic ↥U) (hcard : Nat.card ↥R = 2 * Nat.card ↥U)
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) (hUe : ∀ u ∈ U, u * e = e * u) :
    (if piSign p f then LayerLieType p f Ω e .PSL 3 else LayerLieType p f Ω e .PSU 3) ∨
      LayerLieType p f Ω e .G2 0 ∨ LayerLieType p f Ω e .trialityD4 0 := by
  classical
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_sq_eq_one he2
  obtain ⟨hS, hlt⟩ := genSection_exactPair hp hq hΩ hA hc2 hnc
  set Y := exactLayer Ω e with hY
  have hKΦ : T7H.exactImg Ω e K ∈ oddQuotientFamily (exactPair Ω e) := T7H.exactImg_mem hKt
  have hJΦ : T7H.exactImg Ω e J ∈ oddQuotientFamily (exactPair Ω e) := T7H.exactImg_mem hJt
  have hzK := T7H.isUniqueInvolution_exactCore hp hΩ hc2 hKt hz
  have hjJ := T7H.isUniqueInvolution_exactCore hp hΩ hc2 hJt hj
  have hzY : z ∈ Y := exactCore_le_exactLayer hKt hzK.mem
  have hjY : j ∈ Y := exactCore_le_exactLayer hJt hjJ.mem
  have hdist : T7H.exactImg Ω e J ≠ T7H.exactImg Ω e K := by
    intro h
    have hzb := T7H.exactImg_isUnique hp hΩ hc2 hKt hz hzY
    have hjb := T7H.exactImg_isUnique hp hΩ hc2 hJt hj hjY
    rw [← h] at hzb
    exact hne (T7H.eq_of_toBar_eq hzY hjY hz.sq hj.sq hzj (hzb.eq hjb))
  have hiso : ∀ M ∈ oddQuotientFamily (exactPair Ω e),
      ¬ dAdj (oddQuotientFamily (exactPair Ω e)) (T7H.exactImg Ω e K) M := by
    intro M hM hadj
    obtain ⟨J', hJ't, rfl⟩ := T7H.exists_exactImg_of_mem hM
    have hnb := exactImg_isolated hp hq hΩ hc2 hKt hperp hK't hJ't
    rcases hadj with h | h
    · exact hnb h
    · exact hnb (T3.omegaNbr_symm (l6_2 p f) hp hq hS.hyp hM hKΦ h)
  rcases transSection_or_dConnected hp hq (thm4Below_of_citBelow hn) hlt hS with hconn | htr
  · exfalso
    rcases Relation.ReflTransGen.cases_head (hconn _ hKΦ _ hJΦ) with h | ⟨c, ⟨hcΦ, hadj⟩, -⟩
    · exact hdist h.symm
    · exact hiso c hcΦ hadj
  · have hDE := dEdgeless_of_trans_isolated htr.hyp.conjInvariant htr.trans hKΦ hiso
    have htop := top_notMem_of_trans htr.trans hJΦ hKΦ hdist
    have hRs : IsSylow2In R (exactCore e J) :=
      (isSylow2In_exactCore_iff hΩ hc2 hJt.1 hJt.2).mpr ⟨hRJ, hRe⟩
    have hUN : U ≤ Subgroup.normalizer ((exactCore e K : Subgroup G) : Set G) := by
      intro u hu
      have h1 := exactCore_conjSub u e K
      have h2 : u * e * u⁻¹ = e := by
        rw [hUe u hu]
        group
      rw [h2, mem_normalizer_iff_conjSub_eq.mp (hUK hu)] at h1
      exact mem_normalizer_iff_conjSub_eq.mpr h1.symm
    have hne' : exactCore e J ≠ exactCore e K := fun h => hdist (by unfold T7H.exactImg; rw [h])
    have h1 := omegaStarNbr_subgroupOf_of_data (Λ := exactFamily Ω e)
      (exactCore_le_exactLayer hKt) (exactCore_le_exactLayer hJt) (exactCore_mem_exactFamily hJt)
      hne' hRs hUR hcyc hcard hUN
    have hstarmem := T3.omegaStarNbr_map_quot h1 hdist
    have hstar : ∃ K₀ ∈ oddQuotientFamily (exactPair Ω e),
        (omegaStarNbr (oddQuotientFamily (exactPair Ω e)) K₀).Nonempty :=
      ⟨_, hKΦ, _, hstarmem⟩
    obtain ⟨S₀⟩ : Nonempty (Sylow 2 (↥Y ⧸ classicalInvolutionOddCore ↥Y)) := inferInstance
    obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hp hq htr.hyp S₀
    have hW : (⨆ U ∈ η, U) ∈ WSet (oddQuotientFamily (exactPair Ω e)) := ⟨η, ⟨S₀, hη, hinv⟩, rfl⟩
    have hP : PartIHyp p f (oddQuotientFamily (exactPair Ω e)) :=
      ⟨hp, hq, htr.hyp, htr.aEmpty⟩
    have hS3 : MuIsoS3 (oddQuotientFamily (exactPair Ω e)) (⨆ U ∈ η, U) :=
      MuTab.muIsoS3_of_shape hP hW hDE hstar
    have hrows := ih8MuTableSect_proved (Nat.card G) hn hp hq _ hlt _ htr ⟨_, hKΦ⟩ htop _ hW
    rcases (hrows.2.1).mp hS3 with h | h | h
    · left
      by_cases hπ : piSign p f = true
      · simp only [hπ, ↓reduceIte] at h ⊢
        exact sectionLieType_of_hasLieType hS.gen h
      · simp only [hπ] at h ⊢
        exact sectionLieType_of_hasLieType hS.gen h
    · exact Or.inr (Or.inl (sectionLieType_of_hasLieType hS.gen h))
    · exact Or.inr (Or.inr (sectionLieType_of_hasLieType hS.gen h))

end Layer

end T7X

end CFSG.ClassicalInvolution.Asc77
