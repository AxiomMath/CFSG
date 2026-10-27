module

import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_kFactHyps (hd : D1OneLieData p P M H R Rbar K) :
    ∃ T : Sylow p K, (T : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      IsCatalogGroup K ∧ ¬ IsCyclic (T : Subgroup K) ∧ GLBCore p 1 (T : Subgroup K) ≠ ⊤ ∧
      Nat.card (T : Subgroup K) = Nat.card (d1LiftX p H R K) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  refine ⟨T, hT, hcat, hTnc, hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT, ?_⟩
  have hXp : IsPGroup p ((d1LiftX p H R K).subgroupOf H) :=
    (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
  rw [← Subgroup.card_map_of_injective K.subtype_injective, hT, ← hd.cfg.map_d1LiftX_eq_inf,
    card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (d1LiftX_le_H p H R K)).toEquiv]

theorem D1OneLieData.exists_sylow_of_kZero (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) (hJ : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hne : H₁ ≠ H)
    (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁) :
    ∃ (P' : Sylow p G) (S : Subgroup G), D1Escape p P' M H₁ S ∧ d1LiftX p H R K ≤ S ∧
      Nat.card S ≤ Nat.card R ∧
      (Nat.card S = Nat.card R → Open.pRank p S < Open.pRank p R) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hext := hd.cfg.ext
  set X := d1LiftX p H R K with hXdef
  have hXR : X ≤ R := d1LiftX_le p H R K
  have hXH₁ : X ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH₁
  have hXM : X ≤ M := hXR.trans hext.le_M
  have hX3 := hd.three_le_pRank_d1LiftX hT
  have hH₁M : ¬ H₁ ≤ M := hd.not_le_of_nclIn_le hJH₁
  have hrank : 3 ≤ Open.pRank p (H₁ ⊓ M) :=
    hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hXH₁ hXM))
  obtain ⟨T, hTM, -, -⟩ := intersecting_local_has_contained_sylow p hp P hext.sylow_le
    hext.weakCore_le hrank
  have hXp : IsPGroup p X := hext.isPGroup.to_le hXR
  obtain ⟨S, hS⟩ := (hXp.comap_subtype (K := H₁ ⊓ M)).exists_le_sylow
  set R' : Subgroup G := (S : Subgroup ↥(H₁ ⊓ M)).map (H₁ ⊓ M).subtype with hR'def
  have hXR' : X ≤ R' := by
    rw [hR'def, ← Subgroup.map_subgroupOf_eq_of_le (le_inf hXH₁ hXM)]
    exact Subgroup.map_mono hS
  have hR'HM : R' ≤ H₁ ⊓ M := Subgroup.map_subtype_le _
  have hR'p : IsPGroup p R' := S.isPGroup'.map _
  obtain ⟨S', hS'⟩ := (hR'p.comap_subtype (K := H₁)).exists_le_sylow
  have hR'S' : R' ≤ (S' : Subgroup H₁).map H₁.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hR'HM.trans inf_le_left)]
    exact Subgroup.map_mono hS'
  have hS'eq : (S' : Subgroup H₁).map H₁.subtype = R' := by
    refine (Subgroup.eq_of_le_of_card_ge hR'S' ?_).symm
    rw [Subgroup.card_map_of_injective H₁.subtype_injective, S'.card_eq_multiplicity,
      ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective H₁.subtype_injective]
    exact card_le_card_map_sylow S (T.isPGroup'.map _) (le_inf (Subgroup.map_subtype_le _) hTM)
  have hle : Nat.card R' ≤ Nat.card R := hext.extremal H₁ hH₁.1 hH₁M hrank R' hR'HM hR'p
  have hrk : Nat.card R' = Nat.card R → Open.pRank p R' < Open.pRank p R := by
    intro heq
    by_contra hge
    exact hne (hJ H₁ hH₁ hJH₁ R' (hR'HM.trans inf_le_left) hR'p heq.ge (not_lt.mp hge))
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P hext.sylow_le
    (hR'HM.trans inf_le_right) hR'p
  have hm : (c : G)⁻¹ ∈ M := M.inv_mem c.2
  have hloc' : D1LocalU p ((c : G)⁻¹ • P) M := hd.cfg.loc.conj hm
  have hR'P' : R' ≤ (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) := by
    rw [coe_smul_sylow_eq_map_conj]
    intro x hx
    refine ⟨(MulAut.conj (c : G)).toMonoidHom x, hc ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP'M : (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [coe_smul_sylow_eq_map_conj]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hext.sylow_le hx)) (M.inv_mem hm)
  refine ⟨(c : G)⁻¹ • P, R', ?_, hXR', hle, hrk⟩
  exact
    { prime := hp
      ne_two := hext.ne_two
      sylow_le := hP'M
      weakCore_le := hloc'.core
      maxTwoLocal_M := hext.maxTwoLocal_M
      maxTwoLocal_H := hH₁
      le_H := hR'HM.trans inf_le_left
      le_P := hR'P'
      isSylow := ⟨S', hS'eq⟩
      three_le_pRank := hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp hXR')
      not_le := hH₁M }

structure D1OneLieKZeroData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (P' : Sylow p G)
    (H₁ S : Subgroup G) : Prop where
  data : D1OneLieData p P M H R Rbar K
  escape : D1Escape p P' M H₁ S
  nclIn_le : nclIn H (d1LiftX p H R K) ≤ H₁
  liftX_le : d1LiftX p H R K ≤ S

structure D1KZeroCore (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (P' : Sylow p G)
    (H₁ S : Subgroup G) : Prop where
  data : D1CompCore p P M H R Rbar K
  kProper : CFSG.Open.IsKProper G
  escape : D1Escape p P' M H₁ S
  nclIn_le : nclIn H (d1LiftX p H R K) ≤ H₁
  liftX_le : d1LiftX p H R K ≤ S

namespace D1KZeroCore

variable {P' : Sylow p G} {H₁ S : Subgroup G}

theorem liftX_le_H₁ (hc : D1KZeroCore p P M H R Rbar K P' H₁ S) :
    d1LiftX p H R K ≤ H₁ :=
  (le_nclIn (d1LiftX_le_H p H R K)).trans hc.nclIn_le

theorem eq_one_of_mem_of_normal (hc : D1KZeroCore p P M H R Rbar K P' H₁ S)
    {U : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hU : U.Normal) (hUp : IsPGroup p U)
    {y : H₁ ⧸ primeComplementCore (G := H₁) p} (hyU : y ∈ U)
    (hyJ : y ∈ ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) : y = 1 := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set Jt := ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map π₁ with hJt
  set Xt := ((d1LiftX p H R K).subgroupOf H₁).map π₁ with hXt
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.esc.isPGroup.to_le (d1LiftX_le p H R K)
  have hXtp : IsPGroup p Xt := hXp.comap_subtype.map _
  have hncl : nclIn Jt Xt = Jt :=
    nclIn_map_eq π₁ (le_nclIn (d1LiftX_le_H p H R K)) hc.nclIn_le hd.nclIn_nclIn
  obtain ⟨φ, hφs, hφk, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  have : (U.subgroupOf Jt).Normal := Subgroup.normal_subgroupOf
  rcases eq_top_or_le_ker_of_nclIn_eq hKs hXtp hncl φ hφs hφk (U.subgroupOf Jt) with
    htop | hker
  · exfalso
    have hJp : IsPGroup p Jt := by
      intro j
      obtain ⟨k, hk⟩ := hUp ⟨j, Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top j)⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hKp : IsPGroup p K := hJp.of_surjective φ hφs
    have : Group.IsNilpotent K := hKp.isNilpotent
    obtain ⟨x, y, hxy⟩ := hKnab
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance x y)
  · have hbot : U.subgroupOf Jt ⊓ φ.ker = ⊥ :=
      inf_eq_bot_of_isPGroup hp (hUp.comap_subtype (K := Jt)) hφk
    have hmem : (⟨y, hyJ⟩ : Jt) ∈ U.subgroupOf Jt ⊓ φ.ker :=
      ⟨Subgroup.mem_subgroupOf.mpr hyU, hker (Subgroup.mem_subgroupOf.mpr hyU)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem

end D1KZeroCore

namespace D1OneLieKZeroData

variable {P' : Sylow p G} {H₁ S : Subgroup G}

theorem toCore (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) :
    D1KZeroCore p P M H R Rbar K P' H₁ S :=
  ⟨hc.data.toCore, hc.data.cfg.glob.kProper, hc.escape, hc.nclIn_le, hc.liftX_le⟩

theorem liftX_le_H₁ (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) :
    d1LiftX p H R K ≤ H₁ :=
  (le_nclIn (d1LiftX_le_H p H R K)).trans hc.nclIn_le

theorem eq_one_of_mem_of_normal (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {U : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hU : U.Normal) (hUp : IsPGroup p U)
    {y : H₁ ⧸ primeComplementCore (G := H₁) p} (hyU : y ∈ U)
    (hyJ : y ∈ ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) : y = 1 :=
  hc.toCore.eq_one_of_mem_of_normal hU hUp hyU hyJ

theorem card_map_eq (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) :
    Nat.card ((S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) =
        Nat.card S ∧
      Nat.card (((d1LiftX p H R K).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) = Nat.card (d1LiftX p H R K) := by
  have hp := hc.escape.prime
  have hSp : IsPGroup p S := hc.escape.isPGroup
  refine ⟨?_, ?_⟩
  · rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p)
        (show IsPGroup p (S.subgroupOf H₁) from hSp.comap_subtype),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.escape.le_H).toEquiv]
  · rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p)
        (show IsPGroup p ((d1LiftX p H R K).subgroupOf H₁) from
          (hSp.to_le hc.liftX_le).comap_subtype),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.liftX_le_H₁).toEquiv]

end D1OneLieKZeroData

end CFSG.AGLEmbedding
