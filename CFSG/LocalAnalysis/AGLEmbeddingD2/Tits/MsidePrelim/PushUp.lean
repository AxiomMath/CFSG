module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem D2L34BetaConf3.l34Ctx_of_nine
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9) :
    L34Ctx M H R Rbar K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge hc.esc.A_le
    (by rw [hR9, hc.esc.card_A]; norm_num)
  have hKn : K.Normal := hc.almostSimple.normal
  have hcomp := hc.almostSimple.component
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hc.almostSimple.center_eq_bot).trans
      QuotientGroup.quotientBot).symm
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hcomp.2.2.2
  have hRbarK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ K := by
    rw [hc.rbar, ← hAR]
    exact hc.le_K
  have hRbarcard : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 2 := by
    rw [hc.rbar, ← hAR]
    exact hc.almostSimple.card_A
  have hinf : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := inf_eq_left.mpr hRbarK
  refine
    { normal := hKn
      simple := e.isSimpleGroup
      nonab := ?_
      center := hc.almostSimple.center_eq_bot
      sylow := ?_
      rbar := hc.rbar
      inf_ne_bot := ?_
      mapX := ?_
      isPGroup := ?_
      le_inf := le_inf hc.esc.le_H hc.esc.le_M
      primeCore_le := hc.esc.primeCore_le
      twoCore_le := hc.esc.twoCore_le
      ne_top := fun htop => hc.esc.not_le
        (hc.esc.maxTwoLocal_M.2 H hc.esc.maxTwoLocal_H.1 (htop ▸ le_top)).le
      twoLocal := hc.esc.maxTwoLocal_H.1
      kProper := (D2Amb3.glob (G := G)).kProper
      charTwo := (D2Amb3.glob (G := G)).charTwo
      centralizer_eq_bot := hc.almostSimple.centralizer_eq_bot }
  · obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hcomp.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  · exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
      (ComponentClassification.Components.mathlib_subnormal_of_chain hcomp.2.1
        Subgroup.IsSubnormal.top)
  · rw [hinf]
    intro h
    have := hRbarcard
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  · rw [map_d1LiftX, ← hc.rbar]
  · rw [← hAR]
    exact IsPGroup.of_card (n := 2) hc.esc.card_A

theorem D2L34BetaConf3.l34Ctx
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M) :
    L34Ctx M H R Rbar K :=
  D2L34BetaConf3.l34Ctx_of_nine hc (hc.card_R_eq_nine hstr)

theorem D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf_of_nine
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  have hx := D2L34BetaConf3.l34Ctx_of_nine hc hR9
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hV1 : V ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_H.1
    (le_bot_iff.mp (h ▸ hx.twoCore_le_of_isSylowTwoOf hD₀H hOD hV))
  by_cases hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))
  · exact ⟨thompsonJ V, B6.thompsonJ_le V, Setup.thompsonJ_ne_bot hV.2.1 hV1,
      Setup.characteristic_thompsonJ V, hx.cover_thompsonJ hD₀H hOD hV hα⟩
  · push Not at hα
    obtain ⟨A', hA', a, haA, haC⟩ := hα
    exact ⟨omegaOneCenterOf V, Setup.omegaOneCenterOf_le V,
      Setup.omegaOneCenterOf_ne_bot hV.2.1 hV1, Setup.characteristic_omegaOneCenterOf V,
      hx.cover_omegaOneCenterOf hFF hL hD₀H hOD hV hA' haA haC⟩

theorem D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf_of_nine hFF hc (hc.card_R_eq_nine hstr) hD₀H
    hOD hV

theorem D2L34BetaConf3.exists_char_cover_of_nine
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (_hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf_of_nine hFF hc hR9
    ((glbPrimeCore_le 3 _).trans inf_le_left)
    (D2L34BetaConf3.l34Ctx_of_nine hc hR9).glbPrimeCore_le_inf hV

theorem D2L34BetaConf3.exists_char_cover
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (_hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.exists_char_cover_of_nine hFF hc (hc.card_R_eq_nine hstr) hV _hAV

theorem D2L34BetaConf3.exists_char_cover_syl_of_nine
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf_of_nine hFF hc hR9 inf_le_left
    (le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le) hT

theorem D2L34BetaConf3.exists_char_cover_syl
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf3.exists_char_cover_syl_of_nine hFF hc (hc.card_R_eq_nine hstr) hT

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf.l34Ctx
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M) :
    L34Ctx M H R Rbar K := by
  have := hc.amb3
  exact hc.toConf3.l34Ctx hstr

theorem D2L34BetaConf.exists_char_cover_of_isSylowTwoOf
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  have := hc.amb3
  exact hc.toConf3.exists_char_cover_of_isSylowTwoOf hFF hstr hD₀H hOD
    hV

theorem D2L34BetaConf.exists_char_cover
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (_hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf.exists_char_cover_of_isSylowTwoOf hFF hc hstr
    ((glbPrimeCore_le 3 _).trans inf_le_left)
    (D2L34BetaConf.l34Ctx hc hstr).glbPrimeCore_le_inf hV

theorem D2L34BetaConf.exists_char_cover_syl
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  D2L34BetaConf.exists_char_cover_of_isSylowTwoOf hFF hc hstr inf_le_left
    (le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le) hT

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
