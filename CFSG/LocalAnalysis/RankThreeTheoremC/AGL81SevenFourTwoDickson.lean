module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoSteps
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.ComponentInitial.PerfectNormalizerLayer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Tools
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoSL
import CFSG.RankThree.PartOne.S12.LA126
import CFSG.RankThree.PartOne.S13K.Pair134Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem map_closure_orderOf_eq [Fact p.Prime] {N : Type*} [Group N]
    (ψ : N →* GL (Fin 2) (ZMod p)) :
    (Subgroup.closure {x : N | orderOf x = p}).map ψ = ⊥ ∨
      Nat.card ((Subgroup.closure {x : N | orderOf x = p}).map ψ) = p ∨
      (Subgroup.closure {x : N | orderOf x = p}).map ψ = StatedSL 2 (ZMod p) := by
  have hp : p.Prime := Fact.out
  have heq : (Subgroup.closure {x : N | orderOf x = p}).map ψ =
      Subgroup.closure (ψ '' {x : N | orderOf x = p} \ {1}) := by
    rw [MonoidHom.map_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      · exact Subgroup.subset_closure ⟨hy, hy1⟩
    · exact Subgroup.closure_mono Set.diff_subset
  rw [heq]
  apply CFSG.RankThree.SubgroupLists.dickson_gl_two_closure
  rintro _ ⟨⟨x, hx, rfl⟩, hx1⟩
  have hdvd : orderOf (ψ x) ∣ p := hx ▸ orderOf_map_dvd ψ x
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

theorem closure_orderOf_normal {N : Type*} [Group N] :
    (Subgroup.closure {x : N | orderOf x = p}).Normal :=
  Subgroup.normalizer_eq_top_iff.mp <| top_le_iff.mp <|
    Subgroup.le_normalizer_closure_iff.mpr fun g _ x hx => Subgroup.subset_closure (by
      change orderOf (g * x * g⁻¹) = p
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hx)

theorem normalizer_le_of_isPGroup_map_closure [Fact p.Prime] (P : Sylow p X) {Y D : Subgroup X}
    (e : D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p))
    (hPD : (P : Subgroup X) ≤ Subgroup.normalizer (D : Set X))
    (hW : GLBWeakCore p (P : Subgroup X) ≤ Y) (hPY : (P : Subgroup X) ≤ Y)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup X))
    (hker : (centerQuotientAction D e).ker.map (Subgroup.normalizer (D : Set X)).subtype ≤ Y)
    (hI : IsPGroup p ((Subgroup.closure
      {x : Subgroup.normalizer (D : Set X) | orderOf x = p}).map (centerQuotientAction D e))) :
    Subgroup.normalizer (D : Set X) ≤ Y := by
  have hp : p.Prime := Fact.out
  set N := Subgroup.normalizer (D : Set X) with hN
  set ψ := centerQuotientAction D e with hψ
  set I := Subgroup.closure {x : N | orderOf x = p} with hIdef
  have hIn : I.Normal := closure_orderOf_normal
  set P' : Sylow p N := P.subtype hPD with hP'
  have hP'map : (P' : Subgroup N).map N.subtype = P := by
    rw [hP', Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPD]
  have hf : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have : (I.map ψ.rangeRestrict).Normal := hIn.map _ hf
  have hIf : IsPGroup p (I.map ψ.rangeRestrict) := by
    have h := hI.comap_of_injective ψ.range.subtype ψ.range.subtype_injective
    rwa [show I.map ψ = (I.map ψ.rangeRestrict).map ψ.range.subtype by
        rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict],
      Subgroup.comap_map_eq_self_of_injective ψ.range.subtype_injective] at h
  have hle := hIf.le_sylow_of_normal (P'.mapSurjective hf)
  rw [Sylow.coe_mapSurjective] at hle
  have hIP : I ≤ (P' : Subgroup N) ⊔ ψ.ker := by
    have h := Subgroup.map_le_iff_le_comap.mp hle
    rwa [Subgroup.comap_map_eq, MonoidHom.ker_rangeRestrict] at h
  have hIY : I.map N.subtype ≤ Y := by
    refine (Subgroup.map_mono hIP).trans ?_
    rw [Subgroup.map_sup, hP'map]
    exact sup_le hPY hker
  have hPI : 3 ≤ Open.pRank p ((P : Subgroup X) ⊓ I.map N.subtype) := by
    obtain ⟨F, hFP, hF, hFc⟩ := pRank_attained p hp (P : Subgroup X)
    have hFI : F ≤ (P : Subgroup X) ⊓ I.map N.subtype := by
      intro x hx
      refine ⟨hFP hx, ⟨⟨x, hPD (hFP hx)⟩, ?_, rfl⟩⟩
      by_cases h1 : x = 1
      · have : (⟨x, hPD (hFP hx)⟩ : N) = 1 := Subtype.ext h1
        rw [this]
        exact I.one_mem
      · apply Subgroup.subset_closure
        change orderOf (⟨x, hPD (hFP hx)⟩ : N) = p
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (hF.2 x hx) h1
    exact h3.trans (le_csSup (pRank_bddAbove p hp _) ⟨F, hFI, hF, hFc⟩)
  exact le_of_frattini P hPD (Subgroup.map_subtype_le _) (le_normalizer_map_subtype hIn) hIY
    ((normalizer_le_weakCore p inf_le_left (by omega)
      (hPI.trans (pRank_mono p hp le_sup_left))).trans hW)

theorem exists_perfect_map_eq [Fact p.Prime] (hp5 : 5 ≤ p) {N : Type*} [Group N] [Finite N]
    (ψ : N →* GL (Fin 2) (ZMod p)) {I : Subgroup N} (hI : I.map ψ = StatedSL 2 (ZMod p)) :
    ∃ A : Subgroup N, A ≤ I ∧ Group.IsPerfect A ∧ A.map ψ = StatedSL 2 (ZMod p) := by
  obtain ⟨n, hn⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.exists_isPerfect_derivedSeries I
  set f : I →* GL (Fin 2) (ZMod p) := ψ.comp I.subtype with hf
  have hrange : f.range = StatedSL 2 (ZMod p) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hI]
  have hperf : Group.IsPerfect f.range := by
    rw [hrange]
    exact CFSG.RankThree.PartOne.LA126.isPerfect_statedSL_two hp5
  have hder : derivedSeries f.range n = ⊤ :=
    CFSG.RankThree.PartOne.S13K.derivedSeries_eq_top_of_isPerfect hperf n
  have hmap : (derivedSeries I n).map f = StatedSL 2 (ZMod p) := by
    have h1 := map_derivedSeries_eq (f := f.rangeRestrict) f.rangeRestrict_surjective n
    rw [hder] at h1
    have h2 : ((derivedSeries I n).map f.rangeRestrict).map f.range.subtype = f.range := by
      rw [h1, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2
    rw [h2, hrange]
  refine ⟨(derivedSeries I n).map I.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have : ((derivedSeries I n).map I.subtype) =
        (I.subtype.comp (derivedSeries I n).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact Group.IsPerfect.range _
  · rw [Subgroup.map_map]
    exact hmap

theorem eq_layer_of_isComponent (hL : CFSG.IsComponent (CFSG.layer X)) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : K = CFSG.layer X := by
  by_contra hne
  have hKE : K ≤ CFSG.layer X := le_sSup hK
  have hc := ComponentClassification.LocalComponents.commute_of_ne K (CFSG.layer X)
    ((CFSG.isComponent_iff_open K).mp hK) ((CFSG.isComponent_iff_open _).mp hL) hne
  have hKK : ⁅K, K⁆ = ⊥ := le_bot_iff.mp (hc ▸ Subgroup.commutator_mono le_rfl hKE)
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have hcomm : a * b = b * a := by
    have hmem : ((⁅(a : X), (b : X)⁆ : X)) ∈ ⁅K, K⁆ :=
      Subgroup.commutator_mem_commutator a.2 b.2
    rw [hKK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subtype.ext hmem
  rw [← QuotientGroup.mk_mul, hcomm, QuotientGroup.mk_mul]

theorem le_layer_of_isPerfect_of_isComponent (hSch : KFactCatalogSchreier)
    (hX : CatalogSimpleSections X) (hL : CFSG.IsComponent (CFSG.layer X)) {A : Subgroup X}
    (hA : Group.IsPerfect A) (hAF : ⁅A, CFSG.fittingSubgroup X⁆ = ⊥) : A ≤ CFSG.layer X := by
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  refine CFSG.LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hA
    hAF (fun K hK => ?_) (fun K hK => ?_)
  · rw [eq_layer_of_isComponent hL hK, Subgroup.normalizer_eq_top]
    exact le_top
  · have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2.1
    exact hSch _ inferInstance hK.1.2.2
      (hX.isCatalogGroup_center_quotient ((CFSG.isComponent_iff_open K).mp hK))

theorem normalizer_le_of_map_closure_eq_statedSL (hSch : KFactCatalogSchreier)
    (hX : CatalogSimpleSections X) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcore : primeComplementCore (G := X) p = ⊥) (P : Sylow p X) {Y D : Subgroup X}
    (e : D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p))
    (hL : CFSG.IsComponent (CFSG.layer X)) (hDL : D ≤ CFSG.layer X) (hLY : CFSG.layer X ≤ Y)
    (hPD : (P : Subgroup X) ≤ Subgroup.normalizer (D : Set X))
    (hW : GLBWeakCore p (P : Subgroup X) ≤ Y) (h3 : 3 ≤ Open.pRank p (P : Subgroup X))
    (hcyc : IsCyclic ((P : Subgroup X) ⊓ Subgroup.centralizer (D : Set X) : Subgroup X))
    (hker : (centerQuotientAction D e).ker.map (Subgroup.normalizer (D : Set X)).subtype ≤ Y)
    (hI : (Subgroup.closure {x : Subgroup.normalizer (D : Set X) | orderOf x = p}).map
      (centerQuotientAction D e) = StatedSL 2 (ZMod p)) :
    Subgroup.normalizer (D : Set X) ≤ Y := by
  have hp : p.Prime := Fact.out
  set N := Subgroup.normalizer (D : Set X) with hN
  set ψ := centerQuotientAction D e with hψ
  obtain ⟨A, -, hA, hAmap⟩ := exists_perfect_map_eq hp5 ψ hI
  have hA' : Group.IsPerfect (A.map N.subtype) := by
    have : A.map N.subtype = (N.subtype.comp A.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact Group.IsPerfect.range _
  have hFP : CFSG.fittingSubgroup X ≤ (P : Subgroup X) := by
    rw [CFSG.Fitting_eq_pcore X p hcore]
    exact (CFSG.pCore_isPGroup (p := p) (G := X)).le_sylow_of_normal P
  have hFD : CFSG.fittingSubgroup X ≤ Subgroup.centralizer (D : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := X))).trans (Subgroup.centralizer_le hDL)
  have hAF : ⁅A.map N.subtype, CFSG.fittingSubgroup X⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_isPerfect_of_isCyclic hA' (Subgroup.isCyclic_of_le (le_inf hFP hFD)))
  have hAL := le_layer_of_isPerfect_of_isComponent hSch hX hL hA' hAF
  set S := (StatedSL 2 (ZMod p)).comap ψ with hS
  have hSn : S.Normal := by
    have : (StatedSL 2 (ZMod p)).Normal := by
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
      infer_instance
    exact this.comap ψ
  have hSY : S.map N.subtype ≤ Y := by
    rw [hS, ← hAmap, Subgroup.comap_map_eq, Subgroup.map_sup]
    exact sup_le (hAL.trans hLY) hker
  have hPS : (P : Subgroup X) ≤ S.map N.subtype := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    refine ⟨⟨x, hPD hx⟩, ?_, rfl⟩
    have hxk : (⟨x, hPD hx⟩ : N) ^ p ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    apply CFSG.LocalAnalysis.RankThreeUC.AGL81C.mem_statedSL_of_pow_eq_one (k := k)
    rw [← map_pow, hxk, map_one]
  refine le_of_frattini P hPD (Subgroup.map_subtype_le _) (le_normalizer_map_subtype hSn) hSY ?_
  rw [inf_eq_left.mpr hPS]
  exact (normalizer_le_weakCore_of_rank p hp (P : Subgroup X) h3).trans hW

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
