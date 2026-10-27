module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem map_inf_d1LayerX_le_layer (p : ℕ) (M H R : Subgroup G) :
    ((pCorePreimage p M ⊓ d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
  rintro _ ⟨y, ⟨-, x, ⟨-, hxE⟩, hxy⟩, rfl⟩
  rw [← Subtype.ext hxy]
  exact hxE

theorem D1CaseTwoDataAt.d1X0_le_normalizer_map_inf (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) :
    d1X0 p M H ≤ Subgroup.normalizer ((((pCorePreimage p M ⊓ d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have : (CFSG.layer (H ⧸ primeComplementCore (G := H) p)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hYH : pCorePreimage p M ≤ H := (h3.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  have hA : ((pCorePreimage p M ⊓ d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      d1MapPCore p M H ⊓ CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
    refine le_antisymm (le_inf ?_ (map_inf_d1LayerX_le_layer p M H R)) ?_
    · exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
    · rintro w ⟨hwV, hwE⟩
      rw [h3.d1MapPCore_eq h84 hD2] at hwV
      obtain ⟨r, ⟨hrR, hrY⟩, rfl⟩ := hwV
      exact ⟨r, ⟨hrY, r, ⟨hrR, hwE⟩, rfl⟩, rfl⟩
  rw [hA]
  refine le_trans (le_inf ?_ ?_) Subgroup.inf_normalizer_le_normalizer_inf
  · exact map_le_normalizer_map _ hYH (inf_le_right.trans (le_normalizer_pCorePreimage p M))
  · rw [Subgroup.normalizer_eq_top]
    exact le_top

theorem D1CaseTwoDataAt.exists_component_le_map_nclIn (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥) :
    ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H ∧ L ≤ ((nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hp := hd.cfg.red.prime
  have : (CFSG.layer (H ⧸ primeComplementCore (G := H) p)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hYH : pCorePreimage p M ⊓ d1LayerX p H R ≤ H := inf_le_right.trans (d1LiftX_le_H p H R _)
  have hYR : pCorePreimage p M ⊓ d1LayerX p H R ≤ R := inf_le_right.trans (d1LiftX_le p H R _)
  have hAR : ((pCorePreimage p M ⊓ d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ Rbar := by
    rw [hd.cfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hYR)
  obtain ⟨L, hL, hLN, hLX₀⟩ := hd.cfg.red.exists_component_le_of_normal hd.cyclic
    (map_inf_d1LayerX_le_layer p M H R) hAR
    (map_mk_ne_bot_of_isPGroup hp hYH (hd.cfg.ext.isPGroup.to_le hYR) hY)
    (hd.d1X0_le_normalizer_map_inf hAut hS hKL h84 hD2)
    ((nclIn_normal H _).map _ (QuotientGroup.mk'_surjective _))
    (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hYH)))
    (map_nclIn_le_of_normal p inferInstance (map_inf_d1LayerX_le_layer p M H R))
  exact ⟨L, hL, hLX₀, hLN⟩

theorem D1CaseTwoDataAt.nclIn_nclIn_inf (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥) :
    nclIn (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) (pCorePreimage p M ⊓ d1LayerX p H R) =
      nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set Y := pCorePreimage p M ⊓ d1LayerX p H R with hYdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hYH : Y ≤ H := inf_le_right.trans (d1LiftX_le_H p H R _)
  have hYR : Y ≤ R := inf_le_right.trans (d1LiftX_le p H R _)
  have hYp : IsPGroup p Y := hd.cfg.ext.isPGroup.to_le hYR
  have hYJ : Y ≤ nclIn H Y := le_nclIn hYH
  have h1 := hd.cfg.red.le_nclIn_of_normal hd.cyclic (map_inf_d1LayerX_le_layer p M H R)
    (map_mk_ne_bot_of_isPGroup hp hYH hYp hY) (hd.d1X0_le_normalizer_map_inf hAut hS hKL h84 hD2)
    ((nclIn_normal H Y).map _ (QuotientGroup.mk'_surjective _))
    (Subgroup.map_mono (Subgroup.comap_mono hYJ)) fun W hW hYW => map_nclIn_le_of_normal p hW hYW
  refine nclIn_nclIn_of_map_le hYH hYp (h1.trans (nclIn_le ?_ ?_ ?_))
  · exact Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hYJ))
  · exact Subgroup.map_mono (Subgroup.comap_mono (nclIn_le_self _ Y))
  · exact map_le_normalizer_map π ((nclIn_le_self _ Y).trans (nclIn_le_self H Y))
      (le_normalizer_nclIn _ Y)

theorem D1CaseTwoDataAt.isPerfect_map_nclIn_inf (hd : D1CaseTwoDataAt p P M H R Rbar) :
    Group.IsPerfect ((((nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) := by
  have : (CFSG.layer (H ⧸ primeComplementCore (G := H) p)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  exact Subgroup.isPerfect_iff.mpr (commutator_eq_self_of_le_layer
    (fun K hK => hd.cfg.red.center_eq_bot_of_isCyclic hK (hd.cyclic K hK))
    ((nclIn_normal H _).map _ (QuotientGroup.mk'_surjective _))
    (map_nclIn_le_of_normal p inferInstance (map_inf_d1LayerX_le_layer p M H R)))

end Data

section Class

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem d1CaseTwoPCoreClass_competitorsOn_of {Dat : ∀ H : Subgroup G, Sylow p (H ⧸
    primeComplementCore (G := H) p) → Prop}
    (hAt : ∀ H Rb, Dat H Rb → D1CaseTwoDataAt p P M H R Rb)
    (hcomp : ∀ H Rb, Dat H Rb → ∀ {Y : Subgroup G} {L : Subgroup (H ⧸ primeComplementCore (G := H)
        p)},
      IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M H →
      L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ∀ {H' : Subgroup G}, GLBIsMaxTwoLocal H' → nclIn H Y ≤ H' → R ≤ H' →
        ∃ Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p), Dat H' Rb')
    (hAut : KFactCycAut) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) {Y : Subgroup G}
    (hY : Y ≠ ⊥)
    (hmax : ∀ Y' H₁ : Subgroup G,
      (∃ Rb, Dat H₁ Rb ∧ pCorePreimage p M ⊓ d1LayerX p H₁ R = Y') → Nat.card Y' ≤ Nat.card Y) :
    D1JCompetitorsOn (fun H => ∃ Rb, Dat H Rb ∧ pCorePreimage p M ⊓ d1LayerX p H R = Y) R Y := by
  rintro H₁ ⟨Rb₁, hD₁, rfl⟩ H' hH' hJH' hRH'
  have hd₁ := hAt _ _ hD₁
  have hYH : pCorePreimage p M ⊓ d1LayerX p H₁ R ≤ H₁ := inf_le_right.trans (d1LiftX_le_H p H₁ R _)
  obtain ⟨L, hL, hLX₀, hLJ⟩ := hd₁.exists_component_le_map_nclIn hAut hS hKL h84 hD2 hY
  have hncl := hd₁.nclIn_nclIn_inf hAut hS hKL h84 hD2 hY
  obtain ⟨Rbar', hD'⟩ := hcomp _ _ hD₁ hL hLX₀ hLJ hH' hJH' hRH'
  have hle := hd₁.le_d1LayerX_of_le_of hSch inf_le_right hncl hd₁.isPerfect_map_nclIn_inf
    (hAt _ _ hD') hJH'
  have heq : pCorePreimage p M ⊓ d1LayerX p H₁ R = pCorePreimage p M ⊓ d1LayerX p H' R :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hle) (hmax _ H' ⟨Rbar', hD', rfl⟩)
  refine ⟨⟨Rbar', hD', heq.symm⟩, ?_⟩
  calc nclIn H₁ (pCorePreimage p M ⊓ d1LayerX p H₁ R)
      = nclIn (nclIn H₁ (pCorePreimage p M ⊓ d1LayerX p H₁ R))
          (pCorePreimage p M ⊓ d1LayerX p H₁ R) := hncl.symm
    _ ≤ nclIn H' (pCorePreimage p M ⊓ d1LayerX p H₁ R) :=
      nclIn_le_nclIn_of_le (le_nclIn hYH) hJH'

theorem exists_unique_pCore_of {Dat : ∀ H : Subgroup G, Sylow p (H ⧸ primeComplementCore (G := H)
    p) → Prop}
    (hAt : ∀ H Rb, Dat H Rb → D1CaseTwoDataAt p P M H R Rb)
    (hcomp : ∀ H Rb, Dat H Rb → ∀ {Y : Subgroup G} {L : Subgroup (H ⧸ primeComplementCore (G := H)
        p)},
      IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M H →
      L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ∀ {H' : Subgroup G}, GLBIsMaxTwoLocal H' → nclIn H Y ≤ H' → R ≤ H' →
        ∃ Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p), Dat H' Rb')
    (hAut : KFactCycAut) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : Dat H Rbar) (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥) :
    ∃ (H₀ : Subgroup G) (Rbar₀ : Sylow p (H₀ ⧸ primeComplementCore (G := H₀) p)),
      Dat H₀ Rbar₀ ∧ pCorePreimage p M ⊓ d1LayerX p H₀ R ≠ ⊥ ∧
        D1UniqueOver H₀ R (nclIn H₀ (pCorePreimage p M ⊓ d1LayerX p H₀ R)) := by
  obtain ⟨Y, ⟨H₁, hH₁⟩, hmax⟩ := Set.exists_max_image
    {Y' : Subgroup G | ∃ H₁ : Subgroup G, ∃ Rb, Dat H₁ Rb ∧ pCorePreimage p M ⊓ d1LayerX p H₁ R =
        Y'}
    (fun Y' => Nat.card Y') (Set.toFinite _) ⟨_, H, Rbar, hd, rfl⟩
  have hY' : Y ≠ ⊥ := by
    intro hbot
    have h1 := hmax _ ⟨H, Rbar, hd, rfl⟩
    rw [hbot, Subgroup.card_bot] at h1
    exact hY (Subgroup.eq_bot_of_card_le _ h1)
  obtain ⟨H₀, ⟨Rbar₀, hd₀, rfl⟩, huniq⟩ := exists_unique_of_competitorsOn
    (C := fun H => ∃ Rb, Dat H Rb ∧ pCorePreimage p M ⊓ d1LayerX p H R = Y)
    (fun H₂ ⟨_, hd₂, hY₂⟩ => ⟨(hAt _ _ hd₂).toPhaseThree hAut hS hKL,
      hY₂ ▸ inf_le_right.trans (d1LiftX_le _ _ _ _), hY'⟩)
    (d1CaseTwoPCoreClass_competitorsOn_of hAt hcomp hAut hS hKL hSch h84 hD2 hY'
      fun Y' H₂ h => hmax Y' ⟨H₂, h⟩) hH₁
  exact ⟨H₀, Rbar₀, hd₀, hY', huniq⟩

theorem D1CaseTwoData.exists_unique_pCore (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData p P M H R Rbar) (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥) :
    ∃ (H₀ : Subgroup G) (Rbar₀ : Sylow p (H₀ ⧸ primeComplementCore (G := H₀) p)),
      D1CaseTwoData p P M H₀ R Rbar₀ ∧ pCorePreimage p M ⊓ d1LayerX p H₀ R ≠ ⊥ ∧
        D1UniqueOver H₀ R (nclIn H₀ (pCorePreimage p M ⊓ d1LayerX p H₀ R)) :=
  exists_unique_pCore_of (Dat := fun H Rb => D1CaseTwoData p P M H R Rb) (fun _ _ hd => hd.toAt)
    (fun _ _ hd _ _ hL hLX₀ hLJ _ hH' hJH' hRH' => hd.competitor_of hβ hα h3 hS hInv hSch hL hLX₀
        hLJ hH'
      hJH' hRH') (kFactCycAut_of_kFactBeta hβ) hS hKL hSch h84 hD2 hd hY

end Class

end CFSG.AGLEmbedding
