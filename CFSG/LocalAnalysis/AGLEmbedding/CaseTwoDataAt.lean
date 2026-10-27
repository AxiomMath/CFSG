module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedA
public import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

structure D1CaseTwoDataAt (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfigU p P M H R Rbar
  cyclic : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  rank : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3
  neSylow : ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → R ≠ (P : Subgroup G)

theorem D1CaseTwoData.toAt {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData p P M H R Rbar) :
    D1CaseTwoDataAt p P M H R Rbar := by
  refine ⟨hd.cfg.toU, hd.cyclic, hd.rank, fun z hz hnSP h => hnSP ?_⟩
  obtain ⟨-, -, -, -, -, hRz, -⟩ := id hz
  exact (betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P).trans
    (pRank_mono p hd.cfg.red.prime (h ▸ hRz))

end Defs

@[expose] def KFactCycAut : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (R : Sylow p X) (X₀ : Subgroup X),
    ReducedNongeneration p X R X₀ → CatalogSimpleSections X → CycAutRankLeTwo p X R

theorem kFactCycAut_of_kFactBeta (hβ : KFactBeta) : KFactCycAut :=
  fun _ _ _ _ _ _ h hX => h.cycAutRankLeTwo_of_kFactBeta hX hβ

@[expose] def KFactCaseTwoInvIn (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal] (K : Subgroup (H ⧸ N)), Open.IsQuasisimple K →
    Subgroup.center K = ⊥ → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    ∀ p : ℕ, (p = 3 ∨ p = 5) → ∀ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) →
      GLBCore p 1 (T : Subgroup K) ≠ ⊤ → Open.pRank p (⊤ : Subgroup K) ≤ 2 →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
        ∀ f : A →* L, ¬ Function.Surjective f

theorem kFactCaseTwoInvIn_of_kFactCaseTwoInv {G : Type} [Group G] [Finite G]
    (hInv : KFactCaseTwoInv) : KFactCaseTwoInvIn G :=
  fun _ _ _ K _ _ hs hn hc p hp T hT hΓ hr A L _ hL f => hInv K hs hn hc p hp T hT hΓ hr A L hL f

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfigU.exists_isComponentOf (h : D1ComponentConfigU p P M H R Rbar) :
    ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ := by
  obtain ⟨K, hK, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component h.glob.kProper H
    h.ext.ne_top p h.ext.prime h.notCon
  exact ⟨K, hK⟩

theorem D1ComponentConfigU.toPhaseThree (h : D1ComponentConfigU p P M H R Rbar)
    (hU : UPrimeHyp p (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))) :
    D1PhaseThree p P M H R :=
  h.ext.toPhaseThreeU h.glob.toAGLGlobal
    (h.ext.primeCore_inf_eq_iff.mpr (h.red.primeComplementCore_eq_bot_of_uPrimeHyp hU))

theorem D1ComponentConfigU.toPhaseThree_of_isCyclic (hcfg : D1ComponentConfigU p P M H R Rbar)
    (hcyc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hU : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      (∃ U₀ : Subgroup (H ⧸ primeComplementCore (G := H) p),
        U₀ ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L ∧ Nat.card U₀ = p ∧
        L ⊓ Subgroup.normalizer (U₀ : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) ∧
      KFactUPrime p ↥L) :
    D1PhaseThree p P M H R :=
  hcfg.toPhaseThree (uPrimeHyp_of_isCyclic hcfg.red.prime Rbar fun L hL hLX₀ =>
    ⟨hcyc L hL, hU L hL hLX₀⟩)

theorem D1ComponentConfigU.centralizer_not_le (hcfg : D1ComponentConfigU p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hLX : ¬ L ≤ d1X0 p M H) {z : G}
    (hzH : z ∈ H) (hzp : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hp := hcfg.red.prime
  have hO := primeComplementCore_coprime (G := H) p
  intro hle
  obtain ⟨ℓ, hℓL, hℓX₀⟩ := Set.not_subset.mp hLX
  have hzH' : orderOf (⟨z, hzH⟩ : H) = p := (Subgroup.orderOf_coe _).symm.trans hzp
  obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq hp _ hO
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzL ℓ hℓL))
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  exact hℓX₀ ⟨g, ⟨g.2, hle hgC⟩, rfl⟩

end Config

theorem layer_le_of_forall_inf_ne_bot {Y : Type*} [Group Y] {S : Subgroup Y}
    (hsimple : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsSimpleGroup L)
    (hN : CFSG.layer Y ≤ Subgroup.normalizer (S : Set Y))
    (hS : ∀ L : Subgroup Y, IsComponentOf L ⊤ → S ⊓ L ≠ ⊥) : CFSG.layer Y ≤ S := by
  refine sSup_le fun L hL => ?_
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hLN : L ≤ Subgroup.normalizer (S : Set Y) := (le_layer_of_isComponentOf hL').trans hN
  have : IsSimpleGroup L := hsimple L hL'
  have h : S ⊓ L = L := eq_of_le_normalizer_of_isSimpleGroup inf_le_right
    ((le_inf hLN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
    (hS L hL')
  exact h.symm.le.trans inf_le_left

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_not_le
    (hAut : KFactCycAut)
    (hd : D1CaseTwoDataAt p P M H R Rbar) :
    ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H :=
  hd.cfg.red.exists_not_le_of_caseTwo_of_exists_component
    (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog) hd.cyclic
    hd.cfg.exists_isComponentOf

theorem D1ComponentConfigU.toPhaseThree_of_rank
    (hAut : KFactCycAut) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hcfg : D1ComponentConfigU p P M H R Rbar)
    (hcyc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hrank : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3) :
    D1PhaseThree p P M H R := by
  have hp := hcfg.red.prime
  refine hcfg.toPhaseThree_of_isCyclic hcyc fun L hL hLX₀ => ?_
  obtain ⟨t, ht, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hcfg.red.ne_two hcfg.red.core_eq_bot Rbar hL
  refine ⟨⟨Subgroup.zpowers t, Subgroup.zpowers_le.mpr ht, by rw [Nat.card_zpowers, htp],
    hcfg.red.inf_normalizer_zpowers_le_of_aut (hAut _ _ _ _ hcfg.red hcfg.catalog)
      hcyc hrank hL ht htp⟩, ?_⟩
  exact (hKL p _ (hcfg.red.isCaseTwoGroup_of_not_le_of_aut hcfg.catalog
    (hAut _ _ _ _ hcfg.red hcfg.catalog) hS hcyc hrank hL hLX₀)).1

theorem D1CaseTwoDataAt.toPhaseThree
    (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataAt p P M H R Rbar) : D1PhaseThree p P M H R :=
  hd.cfg.toPhaseThree_of_rank hAut hS hKL hd.cyclic hd.rank

theorem D1CaseTwoDataAt.d1LayerX_ne_bot (hd : D1CaseTwoDataAt p P M H R Rbar) :
    d1LayerX p H R ≠ ⊥ := by
  have hp := hd.cfg.red.prime
  obtain ⟨K, hK⟩ := hd.cfg.exists_isComponentOf
  obtain ⟨t, ⟨htR, htK⟩, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hd.cfg.red.ne_two hd.cfg.red.core_eq_bot Rbar hK
  rw [hd.cfg.rbar] at htR
  obtain ⟨r, hr, hrt⟩ := htR
  intro hbot
  have hrX : (r : G) ∈ d1LayerX p H R :=
    ⟨r, ⟨hr, show QuotientGroup.mk' _ r ∈ CFSG.layer _ from
      hrt ▸ le_layer_of_isComponentOf hK htK⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hrX
  have hr1 : r = 1 := Subtype.ext hrX
  rw [hr1, map_one] at hrt
  rw [← hrt, orderOf_one] at htp
  exact hp.one_lt.ne htp

theorem D1CaseTwoDataAt.isSimpleGroup (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) :
    IsSimpleGroup L :=
  (hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL (hd.cyclic L hL)).1

theorem D1CaseTwoDataAt.map_d1LayerX_inf_ne_bot (hd : D1CaseTwoDataAt p P M H R Rbar)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (hL : IsComponentOf L ⊤) :
    ((d1LayerX p H R).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      L ≠ ⊥ := by
  have hp := hd.cfg.red.prime
  obtain ⟨t, ⟨htR, htL⟩, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hd.cfg.red.ne_two hd.cfg.red.core_eq_bot Rbar hL
  have hX : ((d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        CFSG.layer (H ⧸ primeComplementCore (G := H) p) :=
    hd.cfg.map_d1LiftX_eq_inf
  intro hbot
  have ht : t ∈ ((d1LayerX p H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L := by
    rw [hX]
    exact ⟨⟨htR, le_layer_of_isComponentOf hL htL⟩, htL⟩
  rw [hbot, Subgroup.mem_bot] at ht
  rw [ht, orderOf_one] at htp
  exact hp.one_lt.ne htp

theorem D1CaseTwoDataAt.map_nclIn_eq (hd : D1CaseTwoDataAt p P M H R Rbar) {Y : Subgroup G}
    (hYX : Y ≤ d1LayerX p H R)
    (hY : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
  have : (CFSG.layer (H ⧸ primeComplementCore (G := H) p)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hYH : Y ≤ H := hYX.trans (d1LiftX_le_H p H R _)
  set Eh : Subgroup G := ((CFSG.layer (H ⧸ primeComplementCore (G := H) p)).comap
    (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype
  have hEhH : Eh ≤ H := Subgroup.map_subtype_le _
  have hEhsub : Eh.subgroupOf H = (CFSG.layer (H ⧸ primeComplementCore (G := H) p)).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hHEh : H ≤ Subgroup.normalizer (Eh : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hEhH).mp ?_
    rw [hEhsub]
    exact Subgroup.Normal.comap inferInstance _
  have hYEh : Y ≤ Eh := fun y hy => by
    obtain ⟨x, ⟨-, hxE⟩, rfl⟩ := hYX hy
    exact ⟨x, hxE, rfl⟩
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, ← hEhsub]
    exact Subgroup.comap_mono (nclIn_le hYEh hEhH hHEh)
  · have hJn : (((nclIn H Y).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
      (nclIn_normal H Y).map _ (QuotientGroup.mk'_surjective _)
    refine layer_le_of_forall_inf_ne_bot (fun L hL => hd.isSimpleGroup hL) ?_ fun L hL =>
      ne_bot_of_le_ne_bot (hY L hL)
        (inf_le_inf_right L (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hYH))))
    rw [Subgroup.normalizer_eq_top]
    exact le_top

theorem D1CaseTwoDataAt.not_le_of_nclIn_le
    (hAut : KFactCycAut)
    (hd : D1CaseTwoDataAt p P M H R Rbar)
    {H' : Subgroup G} (hJH' : nclIn H (d1LayerX p H R) ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hAut
  refine hLX₀ ((le_layer_of_isComponentOf hL).trans ?_)
  rw [← hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot]
  exact Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩

theorem D1CaseTwoDataAt.nclIn_nclIn (hd : D1CaseTwoDataAt p P M H R Rbar) :
    nclIn (nclIn H (d1LayerX p H R)) (d1LayerX p H R) = nclIn H (d1LayerX p H R) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hJE := hd.map_nclIn_eq le_rfl hd.map_d1LayerX_inf_ne_bot
  have hXL := hd.map_d1LayerX_inf_ne_bot
  set X := d1LayerX p H R
  set J := nclIn H X
  have hXH : X ≤ H := d1LiftX_le_H p H R _
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R _)
  have hXJ : X ≤ J := le_nclIn hXH
  have hJH : J ≤ H := nclIn_le_self H X
  have hLJ : nclIn J X ≤ J := nclIn_le_self J X
  have hLE : ((nclIn J X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
    refine le_antisymm ((Subgroup.map_mono (Subgroup.comap_mono hLJ)).trans hJE.le) ?_
    exact layer_le_of_forall_inf_ne_bot (fun L hL => hd.isSimpleGroup hL)
      (hJE.ge.trans (map_le_normalizer_map _ (hLJ.trans hJH) (le_normalizer_nclIn J X)))
      fun L hL => ne_bot_of_le_ne_bot (hXL L hL)
        (inf_le_inf_right L (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXJ))))
  have hJLN : J ≤ nclIn J X ⊔ (J ⊓ GLBPrimeCore p H) := by
    intro j hj
    have hjE : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, hJH hj⟩ ∈
        ((nclIn J X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rw [hLE, ← hJE]
      exact Subgroup.mem_map_of_mem _ (show (⟨j, hJH hj⟩ : H) ∈ J.subgroupOf H from hj)
    obtain ⟨l, hl, hlj⟩ := hjE
    have hn : (l : G)⁻¹ * j ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (l⁻¹ * ⟨j, hJH hj⟩)).mp
        (by rw [map_mul, map_inv, hlj, inv_mul_cancel])
    have e : j = l * ((l : G)⁻¹ * j) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl ⟨J.mul_mem (J.inv_mem (hLJ hl)) hj, hn⟩
  have hcop : (Nat.card (J ⊓ GLBPrimeCore p H : Subgroup G)).Coprime p :=
    ((glbPrimeCore_coprime p H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)).symm
  have hconj : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J X := by
    intro c hc x hx
    have hXc : X.map (MulAut.conj c).toMonoidHom ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc) y).mp (hXJ hy)
    exact le_of_le_sup_of_coprime_card_of_le hXc hLJ inf_le_left (nclIn_normal J X)
      (hXp.map _) hcop (hXc.trans hJLN) ⟨x, hx, rfl⟩
  exact le_antisymm hLJ (nclIn_le_of_forall_conj_mem hconj)

theorem D1CaseTwoDataAt.d1LayerX_le_nclIn
    (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    d1LayerX p H R ≤ nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  have heq := (hd.toPhaseThree hAut hS hKL).d1MapPCore_eq h84 hD2
  set X := d1LayerX p H R
  set Y := pCorePreimage p M ⊓ X
  have hXH : X ≤ H := d1LiftX_le_H p H R _
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R _)
  have hYL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥ := by
    intro L hL hbot
    apply hmeet L hL
    rw [eq_bot_iff]
    rintro w ⟨hwV, -, hwL⟩
    rw [heq] at hwV
    obtain ⟨r, ⟨hrR, hrY⟩, rfl⟩ := hwV
    have hr : QuotientGroup.mk' (primeComplementCore (G := H) p) r ∈
        (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L :=
      ⟨⟨r, ⟨hrY, r, ⟨hrR, le_layer_of_isComponentOf hL hwL⟩, rfl⟩, rfl⟩, hwL⟩
    rw [hbot] at hr
    exact hr
  have hJE := hd.map_nclIn_eq inf_le_right hYL
  refine le_of_le_sup_of_coprime_card_of_le hXH (nclIn_le_self H Y) (glbPrimeCore_le p H)
    (nclIn_normal H Y) hXp (glbPrimeCore_coprime p H).symm ?_
  intro x hx
  have hxE : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hXH hx⟩ ∈
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
    obtain ⟨x', ⟨-, hx'E⟩, rfl⟩ := hx
    exact hx'E
  rw [← hJE] at hxE
  obtain ⟨j, hj, hjx⟩ := hxE
  have hn : (j : G)⁻¹ * x ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (j⁻¹ * ⟨x, hXH hx⟩)).mp
      (by rw [map_mul, map_inv, hjx, inv_mul_cancel])
  have e : x = j * ((j : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hj hn

end Data

end CFSG.AGLEmbedding
