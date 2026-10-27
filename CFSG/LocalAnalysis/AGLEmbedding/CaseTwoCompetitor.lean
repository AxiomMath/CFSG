module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.le_d1LayerX_of_le (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {H' : Subgroup G}
    {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hd' : D1CaseTwoDataAt p P M H' R Rbar') (hJH' : nclIn H (d1LayerX p H R) ≤ H') :
    d1LayerX p H R ≤ d1LayerX p H' R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hXH : d1LayerX p H R ≤ H := d1LiftX_le_H p H R _
  have hXR : d1LayerX p H R ≤ R := d1LiftX_le p H R _
  have hXJ : d1LayerX p H R ≤ nclIn H (d1LayerX p H R) := le_nclIn hXH
  set π' := QuotientGroup.mk' (primeComplementCore (G := H') p)
  set Jt := ((nclIn H (d1LayerX p H R)).subgroupOf H').map π'
  set Xt := ((d1LayerX p H R).subgroupOf H').map π'
  obtain ⟨φ, hφ, hcop⟩ :=
    exists_competitorHom_of_map_eq (hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot) hJH'
  have hncl : nclIn Jt Xt = Jt := nclIn_map_eq π' hXJ hJH' hd.nclIn_nclIn
  have hXtp : IsPGroup p Xt :=
    ((hd.cfg.ext.isPGroup.to_le hXR).comap_subtype (K := H')).map π'
  have hXtR : Xt ≤ (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    rw [hd'.cfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXR)
  have hperf : Group.IsPerfect Jt := by
    refine ⟨eq_top_of_map_eq_top_of_nclIn_eq hXtp hncl φ hcop _ ?_⟩
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
      ← commutator_def]
    exact (CFSG.LocalCores.layer_isPerfect
      (G := H ⧸ primeComplementCore (G := H) p)).commutator_eq_top
  have hJN : ∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ →
      Jt ≤ Subgroup.normalizer (L : Set (H' ⧸ primeComplementCore (G := H') p)) := by
    intro L hL
    rw [← hncl]
    exact nclIn_le_of_forall_conj_mem fun c _ x hx =>
      hd'.cfg.red.conj_mem_normalizer_component hL (hXtR hx) c
  obtain ⟨K, hK⟩ := hd'.cfg.exists_isComponentOf
  have hJE := hd'.cfg.red.le_layer_of_isPerfect hd'.cfg.catalog hSch hK hperf hJN
  intro x hx
  have hxH' : x ∈ H' := hJH' (hXJ hx)
  exact ⟨⟨x, hxH'⟩, ⟨hXR hx, hJE ⟨⟨x, hxH'⟩, hXJ hx, rfl⟩⟩, rfl⟩

theorem D1CaseTwoData.le_d1LayerX_of_le (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData p P M H R Rbar) {H' : Subgroup G}
    {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hd' : D1CaseTwoData p P M H' R Rbar') (hJH' : nclIn H (d1LayerX p H R) ≤ H') :
    d1LayerX p H R ≤ d1LayerX p H' R :=
  D1CaseTwoDataAt.le_d1LayerX_of_le (hSch := hSch) (hd := hd.toAt) (hd' := hd'.toAt) (hJH' := hJH')

theorem D1CaseTwoDataAt.forall_isCyclic_of_competitor (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {Y : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hcfg' : D1ComponentConfigU p P M H' R Rbar') (hJH' : nclIn H Y ≤ H')
    (hIII : ∀ K' : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf K' ⊤ →
      (∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ → L = K') →
      ¬ IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ K' :
        Subgroup (H' ⧸ primeComplementCore (G := H') p)) →
      (∀ c ∈ (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓
          Subgroup.centralizer (K' : Set (H' ⧸ primeComplementCore (G := H') p)),
        orderOf c = p → c ∈ (Subgroup.center K').map K'.subtype) → False) :
    ∀ K' : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf K' ⊤ →
      IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ K' :
        Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
  intro K' hK'
  by_contra hnc'
  rcases hcfg'.red.rankOne_or_center hK' hnc' with ⟨z, hzR, hzK, hzp, hzc, -⟩ | hcent
  · exact hd.false_of_rankOne_competitor_of hAut hS hInv hSch hL hLX₀ hLJ hcfg' hJH' hK' hnc'
      ⟨z, hzR, hzK, hzp, hzc⟩
  · exact hIII K' hK' (fun L hL => hcfg'.red.eq_of_forall_mem_center hK' hL hcent) hnc' hcent

theorem D1CaseTwoData.competitor (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData p P M H R Rbar) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H (d1LayerX p H R) ≤ H') (hRH' : R ≤ H') :
    ∃ Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p),
      D1CaseTwoData p P M H' R Rbar' ∧ d1LayerX p H R ≤ d1LayerX p H' R := by
  have hcfg := hd.cfg
  have hext' : D1Extremal p P M H' R := hcfg.ext.of_le hH' hRH' (hd.not_le_of_nclIn_le hβ hJH')
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (d1ConstrainedCase_of_kFactsW hβ hα G hcfg.glob p P M hcfg.loc H' R hext' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := hext'.exists_componentConfig hcfg.glob hcfg.loc hcon hcfg.ind
  obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hβ
  have hall := hd.toAt.forall_isCyclic_of_competitor (kFactCycAut_of_kFactBeta hβ) hS
    (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hL hLX₀
    ((le_layer_of_isComponentOf hL).trans (hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot).ge)
    hcfg'.toU hJH' (h3 G p P M H' R Rbar' hcfg')
  obtain ⟨K, hK⟩ := hcfg'.exists_isComponentOf
  have hd' : D1CaseTwoData p P M H' R Rbar' :=
    ⟨hcfg', hall, hcfg'.red.pRank_eq_three_of_forall_isCyclic hcfg'.catalog hβ hK hall⟩
  exact ⟨Rbar', hd', hd.le_d1LayerX_of_le hSch hd' hJH'⟩

theorem d1CaseTwoClass_competitorsOn_of {Dat : ∀ H : Subgroup G, Sylow p (H ⧸ primeComplementCore
    (G := H) p) → Prop}
    (hAt : ∀ H Rb, Dat H Rb → D1CaseTwoDataAt p P M H R Rb)
    (hcomp : ∀ H Rb, Dat H Rb → ∀ {H' : Subgroup G}, GLBIsMaxTwoLocal H' →
      nclIn H (d1LayerX p H R) ≤ H' → R ≤ H' →
        ∃ Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p), Dat H' Rb' ∧
          d1LayerX p H R ≤ d1LayerX p H' R)
    {X : Subgroup G}
    (hmax : ∀ X' H₁ : Subgroup G, (∃ Rb, Dat H₁ Rb ∧ d1LayerX p H₁ R = X') →
      Nat.card X' ≤ Nat.card X) :
    D1JCompetitorsOn (fun H => ∃ Rb, Dat H Rb ∧ d1LayerX p H R = X) R X := by
  rintro H₁ ⟨Rb₁, hd₁, rfl⟩ H' hH' hJH' hRH'
  obtain ⟨Rbar', hd', hle⟩ := hcomp _ _ hd₁ hH' hJH' hRH'
  have heq : d1LayerX p H₁ R = d1LayerX p H' R :=
    Subgroup.eq_of_le_of_card_ge hle (hmax _ H' ⟨Rbar', hd', rfl⟩)
  refine ⟨⟨Rbar', hd', heq.symm⟩, ?_⟩
  calc nclIn H₁ (d1LayerX p H₁ R)
      = nclIn (nclIn H₁ (d1LayerX p H₁ R)) (d1LayerX p H₁ R) := (hAt _ _ hd₁).nclIn_nclIn.symm
    _ ≤ nclIn H' (d1LayerX p H₁ R) :=
      nclIn_le_nclIn_of_le (le_nclIn (d1LiftX_le_H p H₁ R _)) hJH'

end Data

end CFSG.AGLEmbedding
