module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Strong
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3CyclicInt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

@[expose] def D2L34BetaMSolvableStrong3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → GLBStronglyEmbedded 3 M

@[expose] def D2L34BetaMSolvableCyclic3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → ∀ g : G, g ∉ M →
      3 ∣ Nat.card ↥(M ⊓ GLBConj g M) → CFSG.Open.pRank 3 (M ⊓ GLBConj g M) ≠ 1

theorem D2L34BetaMSolvableCyclic3.toStrong3 (h : D2L34BetaMSolvableCyclic3 G) :
    D2L34BetaMSolvableStrong3 G := by
  intro d P M A H R Rbar K ctx hs
  by_contra hns
  obtain ⟨g, hg, hdvd, hrk⟩ := ctx.exists_cyclic_of_not_stronglyEmbedded hns
  exact h d P M A H R Rbar K ctx hs g hg hdvd hrk

theorem D2L34BetaMSolvableStrong3.toCyclic3 (h : D2L34BetaMSolvableStrong3 G) :
    D2L34BetaMSolvableCyclic3 G := by
  intro d P M A H R Rbar K ctx hs g hg hdvd _
  exact (h d P M A H R Rbar K ctx hs).2.2 g hg hdvd

theorem D2L34BetaMSolvableCenter3.toStrong3 (h : D2L34BetaMSolvableCenter3 G) :
    D2L34BetaMSolvableStrong3 G :=
  fun _ _ _ _ _ _ _ _ ctx hs => d2L34BetaMSide3_stronglyEmbedded_of_center h ctx hs

theorem d2L34BetaMSide3_of_inputs_strong
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hSS : D2L34BetaMSolvableStrong3 G) (hr2 : FFRankTwoInput3 G) (hnc : FFNoncyclicInput3 G)
    (hnonc : D2L34BetaMSideNonConstrainedInput3 G) : D2L34BetaMSide3 G := by
  intro hS hD1 M hM ha hb P A H R hp hMP d Rbar K hc hAll
  have h : D2L34SideCtx3 G d P M A H R Rbar K := ⟨hS, hD1, hM, ha, hb, hp, hMP, hc, hAll⟩
  refine ⟨fun hs => hSS d P M A H R Rbar K h hs, fun hstr => ?_⟩
  have := h.amb
  have hKmax : D2L34Kmax H := D2L34BetaConf3.d2L34Kmax hc hstr hAll.onlyL34At
  obtain ⟨U, hU, hUsyl, hAU, hNHU, hsylU⟩ :=
    D2L34BetaConf3.exists_base_of_cover hFF hc hstr hAll.onlyL34At
  refine exists_s3Parabolic_of_permuted3 ?_
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M
  · obtain ⟨P₀, hP₀M, hP₀, hNn⟩ :=
      exists_normal_order_three_of_ctx3 hFF hI59 hr2 hnc h hstr hcon
    exact d2L34BetaMSidePermuted3_of_orderThree hc hstr hP₀M hP₀ hNn hU hNHU hsylU
  · obtain ⟨P₁, L, hLM, hLn, hP₁L, hP₁c, hperm', hAL, hsimple⟩ :=
      hnonc d P M A H R Rbar K h hstr hKmax hcon U hU hUsyl hAU hNHU hsylU
    exact d2L34BetaMSidePermuted3_of_nonconstrained hc hstr hU hNHU hLM hLn hP₁L hP₁c hperm'
      hAL hsimple

theorem D2L34SideCtx3.stronglyEmbedded_of_normalizers {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K)
    (hN : ∀ x ∈ (P : Subgroup G), orderOf x = 3 →
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M) :
    GLBStronglyEmbedded 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.setting.simple
  have hMtop : M ≠ ⊤ := twoLocal_ne_top h.setting.nonab h.maxLocal.1
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  refine D2Escape.stronglyEmbedded_of_order_p h.conf.esc hMtop ?_
  intro x hxM hx
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    simp
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le 3 P hPM
    (Subgroup.zpowers_le.mpr hxM) hzp
  set x' : G := (m : G) * x * (m : G)⁻¹ with hx'
  have hx'P : x' ∈ (P : Subgroup G) := by
    refine hm ⟨x, Subgroup.mem_zpowers x, ?_⟩
    simp [hx', MulAut.conj_apply]
  have hx'o : orderOf x' = 3 := by
    have h1 := orderOf_injective (MulAut.conj (m : G)).toMonoidHom
      (MulAut.conj (m : G)).injective x
    have h2 : (MulAut.conj (m : G)).toMonoidHom x = x' := by simp [hx', MulAut.conj_apply]
    rw [h2, hx] at h1
    exact h1
  exact normalizer_zpowers_le_of_conj m.2 (hN x' hx'P hx'o)

theorem D2L34SideCtx3.stronglyEmbedded_of_pure {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K)
    (hpure : ∀ x ∈ (P : Subgroup G), orderOf x = 3 →
      3 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x ⊔
        ((P : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)))) :
    GLBStronglyEmbedded 3 M := by
  refine h.stronglyEmbedded_of_normalizers fun x hxP hxo => ?_
  have hQP : Subgroup.zpowers x ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hxP
  have hQ1 : Subgroup.zpowers x ≠ ⊥ := by
    intro hbot
    have : x = 1 := by
      have := Subgroup.mem_zpowers x
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hxo
    omega
  exact (h.threeClause h.sigma P h.core).1 (Subgroup.zpowers x) hQP hQ1
    (by simpa [Subgroup.centralizer, Set.centralizer] using hpure x hxP hxo)

theorem D2L34SideCtx3.exists_impure_of_not_stronglyEmbedded {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hns : ¬ GLBStronglyEmbedded 3 M) :
    ∃ x ∈ (P : Subgroup G), orderOf x = 3 ∧
      CFSG.Open.pRank 3 (Subgroup.zpowers x ⊔
        ((P : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))) < 3 ∧
      ¬ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  by_contra hcon
  push Not at hcon
  refine hns (h.stronglyEmbedded_of_normalizers fun x hxP hxo => ?_)
  by_contra hN
  have hlt := (hcon x hxP hxo)
  by_cases hrank : 3 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x ⊔
      ((P : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)))
  · have hQP : Subgroup.zpowers x ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hxP
    have hQ1 : Subgroup.zpowers x ≠ ⊥ := by
      intro hbot
      have : x = 1 := by
        have := Subgroup.mem_zpowers x
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      rw [this, orderOf_one] at hxo
      omega
    exact hN ((h.threeClause h.sigma P h.core).1 (Subgroup.zpowers x) hQP hQ1
      (by simpa [Subgroup.centralizer, Set.centralizer] using hrank))
  · push Not at hrank
    exact hN (hlt hrank)

end CFSG.LocalAnalysis.RankThreeTheoremC
