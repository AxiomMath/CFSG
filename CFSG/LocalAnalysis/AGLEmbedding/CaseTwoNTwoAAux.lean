module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_nclIn_le_of_normal (p : ℕ) {H Y : Subgroup G}
    {W : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hW : W.Normal)
    (hYW : (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W := by
  rw [Subgroup.map_le_iff_le_comap]
  have e : (nclIn H Y).subgroupOf H =
      Subgroup.normalClosure ((Y.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [e]
  exact Subgroup.normalClosure_le_normal (N := W.comap _) fun y hy =>
    Subgroup.mem_comap.mpr (hYW (Subgroup.mem_map_of_mem _ hy))

theorem nclIn_nclIn_of_map_le {p : ℕ} [Fact p.Prime] {H Y : Subgroup G} (hYH : Y ≤ H)
    (hYp : IsPGroup p Y)
    (hle : ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      ((nclIn (nclIn H Y) Y).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    nclIn (nclIn H Y) Y = nclIn H Y := by
  set J := nclIn H Y
  have hYJ : Y ≤ J := le_nclIn hYH
  have hJH : J ≤ H := nclIn_le_self H Y
  have hLJ : nclIn J Y ≤ J := nclIn_le_self J Y
  have hJLN : J ≤ nclIn J Y ⊔ (J ⊓ GLBPrimeCore p H) := by
    intro j hj
    obtain ⟨l, hl, hlj⟩ := hle (Subgroup.mem_map_of_mem _
      (show (⟨j, hJH hj⟩ : H) ∈ J.subgroupOf H from hj))
    have hn : (l : G)⁻¹ * j ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (l⁻¹ * ⟨j, hJH hj⟩)).mp
        (by rw [map_mul, map_inv, hlj, inv_mul_cancel])
    have e : j = l * ((l : G)⁻¹ * j) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl ⟨J.mul_mem (J.inv_mem (hLJ hl)) hj, hn⟩
  have hcop : (Nat.card (J ⊓ GLBPrimeCore p H : Subgroup G)).Coprime p :=
    ((glbPrimeCore_coprime p H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)).symm
  have hconj : ∀ c ∈ H, ∀ y ∈ Y, c * y * c⁻¹ ∈ nclIn J Y := by
    intro c hc y hy
    have hYc : Y.map (MulAut.conj c).toMonoidHom ≤ J := by
      rintro _ ⟨y', hy', rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H Y hc) y').mp (hYJ hy')
    exact le_of_le_sup_of_coprime_card_of_le hYc hLJ inf_le_left (nclIn_normal J Y)
      (hYp.map _) hcop (hYc.trans hJLN) ⟨y, hy, rfl⟩
  exact le_antisymm hLJ (nclIn_le_of_forall_conj_mem hconj)

end General

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData.competitor_of (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData p P M H R Rbar) {Y : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H Y ≤ H') (hRH' : R ≤ H') :
    ∃ Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p), D1CaseTwoData p P M H' R Rbar' := by
  have hcfg := hd.cfg
  have hH'M : ¬ H' ≤ M := fun hH'M => hLX₀ (hLJ.trans
    (Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩))
  have hext' : D1Extremal p P M H' R := hcfg.ext.of_le hH' hRH' hH'M
  by_cases hcon : HasPrimeConstraint (G := H') p
  · exact (d1ConstrainedCase_of_kFactsW hβ hα G hcfg.glob p P M hcfg.loc H' R hext' hcon).elim
  obtain ⟨Rbar', hcfg'⟩ := hext'.exists_componentConfig hcfg.glob hcfg.loc hcon hcfg.ind
  have hall := hd.toAt.forall_isCyclic_of_competitor (kFactCycAut_of_kFactBeta hβ) hS
    (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hL hLX₀ hLJ hcfg'.toU hJH'
    (h3 G p P M H' R Rbar' hcfg')
  obtain ⟨K, hK⟩ := hcfg'.exists_isComponentOf
  exact ⟨Rbar', hcfg', hall, hcfg'.red.pRank_eq_three_of_forall_isCyclic hcfg'.catalog hβ hK hall⟩

theorem D1CaseTwoDataAt.le_d1LayerX_of_le_of (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {Y : Subgroup G} (hYX : Y ≤ d1LayerX p H R)
    (hncl : nclIn (nclIn H Y) Y = nclIn H Y)
    (hperf : Group.IsPerfect ((((nclIn H Y).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
        Subgroup (H ⧸ primeComplementCore (G := H) p))))
    {H' : Subgroup G} {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hd' : D1CaseTwoDataAt p P M H' R Rbar') (hJH' : nclIn H Y ≤ H') :
    Y ≤ d1LayerX p H' R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hYH : Y ≤ H := hYX.trans (d1LiftX_le_H p H R _)
  have hYR : Y ≤ R := hYX.trans (d1LiftX_le p H R _)
  have hYJ : Y ≤ nclIn H Y := le_nclIn hYH
  set π' := QuotientGroup.mk' (primeComplementCore (G := H') p)
  set Jt := ((nclIn H Y).subgroupOf H').map π'
  set Yt := (Y.subgroupOf H').map π'
  obtain ⟨φ, hφ, hcop⟩ := exists_competitorHom_of_map_eq rfl hJH'
  have hncl' : nclIn Jt Yt = Jt := nclIn_map_eq π' hYJ hJH' hncl
  have hYtp : IsPGroup p Yt :=
    ((hd.cfg.ext.isPGroup.to_le hYR).comap_subtype (K := H')).map π'
  have hYtR : Yt ≤ (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    rw [hd'.cfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hYR)
  have hperf' : Group.IsPerfect Jt := by
    refine ⟨eq_top_of_map_eq_top_of_nclIn_eq hYtp hncl' φ hcop _ ?_⟩
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
      ← commutator_def]
    exact hperf.commutator_eq_top
  have hJN : ∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ →
      Jt ≤ Subgroup.normalizer (L : Set (H' ⧸ primeComplementCore (G := H') p)) := by
    intro L hL
    rw [← hncl']
    exact nclIn_le_of_forall_conj_mem fun c _ x hx =>
      hd'.cfg.red.conj_mem_normalizer_component hL (hYtR hx) c
  obtain ⟨K, hK⟩ := hd'.cfg.exists_isComponentOf
  have hJE := hd'.cfg.red.le_layer_of_isPerfect hd'.cfg.catalog hSch hK hperf' hJN
  intro x hx
  have hxH' : x ∈ H' := hJH' (hYJ hx)
  exact ⟨⟨x, hxH'⟩, ⟨hYR hx, hJE ⟨⟨x, hxH'⟩, hYJ hx, rfl⟩⟩, rfl⟩

end Data

end CFSG.AGLEmbedding
