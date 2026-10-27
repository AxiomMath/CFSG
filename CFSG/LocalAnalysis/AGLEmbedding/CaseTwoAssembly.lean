module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedB
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoZZFive

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoEscaping : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥ →
      pCorePreimage p M ⊓ R ≠ ⊥ → False

theorem exists_unique_layer_of {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M R : Subgroup G} {Dat : ∀ H : Subgroup G, Sylow p (H ⧸ primeComplementCore (G := H)
    p) → Prop}
    (hAt : ∀ H Rb, Dat H Rb → D1CaseTwoDataAt p P M H R Rb)
    (hcomp : ∀ H Rb, Dat H Rb → ∀ {H' : Subgroup G}, GLBIsMaxTwoLocal H' →
      nclIn H (d1LayerX p H R) ≤ H' → R ≤ H' →
        ∃ Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p), Dat H' Rb' ∧
          d1LayerX p H R ≤ d1LayerX p H' R)
    (hAut : KFactCycAut) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) {H : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : Dat H Rbar) :
    ∃ (H₀ : Subgroup G) (Rbar₀ : Sylow p (H₀ ⧸ primeComplementCore (G := H₀) p)),
      Dat H₀ Rbar₀ ∧ D1UniqueOver H₀ R (nclIn H₀ (d1LayerX p H₀ R)) := by
  obtain ⟨X, ⟨H₁, hH₁⟩, hmax⟩ := Set.exists_max_image
    {X' : Subgroup G | ∃ H₁ : Subgroup G, ∃ Rb, Dat H₁ Rb ∧ d1LayerX p H₁ R = X'}
    (fun X' => Nat.card X') (Set.toFinite _) ⟨d1LayerX p H R, H, Rbar, hd, rfl⟩
  obtain ⟨H₀, ⟨Rbar₀, hd₀, rfl⟩, huniq⟩ := exists_unique_of_competitorsOn
    (C := fun H => ∃ Rb, Dat H Rb ∧ d1LayerX p H R = X)
    (fun H₂ ⟨_, hd₂, hX₂⟩ => ⟨(hAt _ _ hd₂).toPhaseThree hAut hS hKL, hX₂ ▸ d1LiftX_le _ _ _ _,
      hX₂ ▸ (hAt _ _ hd₂).d1LayerX_ne_bot⟩)
    (d1CaseTwoClass_competitorsOn_of hAt hcomp fun X' H₂ h => hmax X' ⟨H₂, h⟩) hH₁
  exact ⟨H₀, Rbar₀, hd₀, huniq⟩

theorem d1CaseTwoRankThree_of_unique (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (hU : D1CaseTwoUnique) : D1CaseTwoRankThree := by
  intro G _ _ p P M H R Rbar hcfg hcyc hrank
  obtain ⟨H₀, Rbar₀, hd₀, huniq⟩ := exists_unique_layer_of
    (Dat := fun H Rb => D1CaseTwoData p P M H R Rb) (fun _ _ hd => hd.toAt)
    (fun _ _ hd _ hH' hJH' hRH' => hd.competitor hβ hα h3 hS hInv hSch hH' hJH' hRH')
    (kFactCycAut_of_kFactBeta hβ) hS hKL (⟨hcfg, hcyc, hrank⟩ : D1CaseTwoData p P M H R Rbar)
  exact hU G p P M H₀ R Rbar₀ hd₀ huniq

theorem D1CaseTwoDataAt.false_of_forall_not_le (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoDataAt p P M H R Rbar) (huniq : D1UniqueOver H R (nclIn H (d1LayerX p H R)))
    (h2 : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H)
    (hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥)
    (hzz : ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ¬ IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = p →
        QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ → False) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hZ := hd.false_of_centralizer_le hAut hS hKL h84 hCGT hD2 huniq hmeet
  have hiso : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCaseTwoGroup p L := fun L hL =>
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog
      (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog) hS hd.cyclic hd.rank hL (h2 L hL)
  have hpt : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ∃ t, t ∈ d1MapPCore p M H ∧
        t ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L ∧ orderOf t = p := by
    intro L hL
    obtain ⟨t, ht, htp, -⟩ := exists_mem_centralizer_orderOf_eq
      (Rbar.isPGroup'.to_le (inf_le_right.trans inf_le_left)) (hmeet L hL)
    exact ⟨t, ht.1, ht.2, htp⟩
  obtain ⟨L₁, hL₁⟩ := hd.cfg.exists_isComponentOf
  obtain ⟨t₁, ht₁V, ht₁, ht₁p⟩ := hpt L₁ hL₁
  have hC₁ : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      Subgroup.centralizer ({t₁} : Set (H ⧸ primeComplementCore (G := H) p)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht₁V)
  by_cases htwo : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₂ ⊤ ∧
      L₂ ≠ L₁
  · obtain ⟨L₂, hL₂, hne⟩ := htwo
    obtain ⟨t₂, ht₂V, ht₂, ht₂p⟩ := hpt L₂ hL₂
    refine hZ ((le_inf hC₁ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht₂V))).trans ?_)
    exact hd.cfg.red.centralizer_le_of_two_components hKL hd.cyclic hL₁ hL₂ (Ne.symm hne)
      (h2 L₁ hL₁) (hiso L₁ hL₁) (hiso L₂ hL₂) ht₁ ht₁p ht₂ ht₂p
  push Not at htwo
  by_cases hA : d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥
  · by_cases hW :
        IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p)))
    · exact hZ (hC₁.trans (hd.cfg.red.centralizer_le_of_isPGroup hKL hd.cyclic hL₁ (hiso L₁ hL₁)
        hW ht₁ ht₁p))
    · obtain ⟨z, hzR, hzp, hzO⟩ := hd.exists_mem_pCore hAut hL₁ htwo
      exact hzz L₁ hL₁ htwo (hmeet L₁ hL₁) hA hW z hzR hzp hzO
        (hd.mem_nclIn_of_unique hAut hS hKL h84 hCGT hD2 huniq hL₁ htwo (hmeet L₁ hL₁) hzR hzp hzO)
  · obtain ⟨z, hz, hzp, -⟩ := exists_mem_centralizer_orderOf_eq
      (CFSG.pCore_isPGroup.to_le inf_le_right) hA
    refine hZ ((le_inf hC₁ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz.1))).trans ?_)
    exact hd.cfg.red.centralizer_le_of_mem_pCore hKL hd.cyclic hL₁ htwo (h2 L₁ hL₁) (hiso L₁ hL₁)
      ht₁ ht₁p hz.2 hzp

theorem D1CaseTwoDataAt.false_of_unique (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoDataAt p P M H R Rbar) (huniq : D1UniqueOver H R (nclIn H (d1LayerX p H R)))
    (h0 : pCorePreimage p M ⊓ R = ⊥ → False)
    (hesc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥ →
      pCorePreimage p M ⊓ R ≠ ⊥ → False)
    (h2a : ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False)
    (hzz : ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ¬ IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = p →
        QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ → False) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hV : pCorePreimage p M ⊓ R = ⊥
  · exact h0 hV
  by_cases he : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥
  · obtain ⟨L, hL, hLX₀, hVL⟩ := he
    exact hesc L hL hLX₀ hVL hV
  push Not at he
  by_cases h2 : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₂ ⊤ ∧
      L₂ ≤ d1X0 p M H
  · obtain ⟨L₂, hL₂, hL₂X₀⟩ := h2
    obtain ⟨L₁, hL₁, hL₁X₀⟩ := hd.exists_not_le hAut
    exact h2a L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ (he L₁ hL₁ hL₁X₀)
  push Not at h2
  have hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥ :=
    fun L hL => he L hL (h2 L hL)
  exact hd.false_of_forall_not_le hAut hS hKL h84 hD2 hCGT huniq h2 hmeet hzz

theorem d1CaseTwoUnique_of (hβ : KFactBeta) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (h0 : D1CaseTwoPosZero) (h2a : D1CaseTwoPosNTwoA) (hzz : D1CaseTwoZZ)
    (hesc : D1CaseTwoEscaping) : D1CaseTwoUnique := fun G _ _ p P M H R Rbar hd huniq =>
  hd.toAt.false_of_unique (kFactCycAut_of_kFactBeta hβ) hS hKL h84 hD2 hCGT huniq
    (h0 G p P M H R Rbar hd huniq) (hesc G p P M H R Rbar hd) (h2a G p P M H R Rbar hd huniq)
    (hzz G p P M H R Rbar hd huniq)

theorem d1CaseTwoRankThree_of (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (h0 : D1CaseTwoPosZero) (h2a : D1CaseTwoPosNTwoA) (hz3 : D1CaseTwoZZThree)
    (hesc : D1CaseTwoEscaping) : D1CaseTwoRankThree :=
  d1CaseTwoRankThree_of_unique hβ hα h3 hS hKL hInv hSch
    (d1CaseTwoUnique_of hβ hS hKL h84 hD2 hCGT h0 h2a
      (d1CaseTwoZZ_of_zzThree hβ hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hz3) hesc)

end CFSG.AGLEmbedding
