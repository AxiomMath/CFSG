module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeOf
public import CFSG.Goldschmidt.Steps.Sec82e

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaOneCenterE (p : ℕ) (U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ U ∧ (∀ u ∈ U, u * x = x * u) ∧ x ^ p = 1}
  one_mem' := ⟨U.one_mem, fun u _ => by simp, one_pow p⟩
  mul_mem' := by
    rintro x y ⟨hx, hxc, hxp⟩ ⟨hy, hyc, hyp⟩
    refine ⟨U.mul_mem hx hy, fun u hu => ?_, ?_⟩
    · rw [← mul_assoc, hxc u hu, mul_assoc, hyc u hu, mul_assoc]
    · rw [(Commute.mul_pow (hyc x hx) p), hxp, hyp, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxc, hxp⟩
    refine ⟨U.inv_mem hx, fun u hu => ?_, by rw [inv_pow, hxp, inv_one]⟩
    have := hxc u hu
    calc u * x⁻¹ = x⁻¹ * (x * u) * x⁻¹ := by group
      _ = x⁻¹ * (u * x) * x⁻¹ := by rw [this]
      _ = x⁻¹ * u := by group


theorem normalizer_le_normalizer_omegaOneCenterE (p : ℕ) (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (omegaOneCenterE p U : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨hx, hxc, hxp⟩
  have hgU := Subgroup.mem_normalizer_iff.mp hg
  refine ⟨(hgU x).mp hx, fun u hu => ?_, by rw [conj_pow, hxp]; group⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (hgU (g⁻¹ * u * g)).mpr (by simpa [mul_assoc] using hu)
    exact this
  have h := hxc _ hu'
  calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * u := by group

theorem normalizer_le_of_isAGLQ_escape {p : ℕ} {P : Sylow p G} {M H R U : Subgroup G}
    (hext : D1Escape p P M H R) (hU : IsAGLQ p M U) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  classical
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hUM, hUp, hU3⟩ := hU
  have rank3 : 3 ≤ Open.pRank p U → Subgroup.normalizer (U : Set G) ≤ M := by
    intro h3
    obtain ⟨m, hm, hUP⟩ := exists_conj_le hext.sylow_le hUp hUM
    exact (normalizer_le_weakCore p hUP (by omega)
      (h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left))).trans
      (weakCore_conj_le hp hext.weakCore_le hm)
  by_cases h3 : 3 ≤ Open.pRank p U
  · exact rank3 h3
  rcases hU3 with h | ⟨E, hEU, hEab, hEc, hΓ⟩
  · exact absurd (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h) h3
  set F := omegaOneCenterE p U with hF
  have hFE : F ≤ E := by
    rintro x ⟨hx, hxc, hxp⟩
    by_contra hxE
    obtain ⟨hab, hcard⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEc hEab.2 hxp hxE
      (fun e he => hxc e (hEU he))
    exact h3 (le_csSup (pRank_bddAbove p hp U)
      ⟨_, sup_le hEU ((Subgroup.zpowers_le).mpr hx), hab, hcard⟩)
  have : Nontrivial U := by
    have h1 : 1 < Nat.card U := by
      have := Subgroup.card_le_of_le hEU
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  have := hUp.center_nontrivial
  obtain ⟨n, hn, hcn⟩ := (hUp.to_subgroup (Subgroup.center U)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (G := Subgroup.center U)
    (by rw [hcn]; exact dvd_pow_self p hn.ne')
  set x : G := ((z : U) : G) with hx
  have hxF : x ∈ F := by
    refine ⟨(z : U).2, fun u hu => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨u, hu⟩
      exact congrArg Subtype.val this
    · have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have := congrArg (fun w : Subgroup.center U => ((w : U) : G)) this
      simpa [hx] using this
  have hx1 : x ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext (by simpa [hx] using h))
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hF1 : 1 ≤ Open.pRank p F := by
    have hxp : x ^ p = 1 := hxF.2.2
    refine le_csSup (pRank_bddAbove p hp F) ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).mpr hxF,
      ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := hy
      simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  exact (normalizer_le_normalizer_omegaOneCenterE p U).trans
    ((le_sSup ⟨F, hFE, hF1, rfl⟩ : Subgroup.normalizer (F : Set G) ≤ GLBCore p 1 E).trans hΓ)

theorem isSylowIn_of_isSylowIn_inf {p : ℕ} [hp : Fact p.Prime] {M H R : Subgroup G}
    (hR : IsSylowIn p R (H ⊓ M)) (hN : Subgroup.normalizer (R : Set G) ≤ M) : IsSylowIn p R H := by
  obtain ⟨S, hS, hRS⟩ := exists_isSylowIn_ge p (hR.le.trans inf_le_left) hR.isPGroup
  by_cases heq : R = S
  · exact heq ▸ hS
  exfalso
  have hSp : IsPGroup p ↥S := hS.isPGroup
  haveI : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hlt : R.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => heq (le_antisymm hRS fun s hs => ?_)
    have : (⟨s, hs⟩ : ↥S) ∈ R.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyR⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  have hyNG : (y : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have h := (Subgroup.mem_normalizer_iff.mp hyN ⟨r, hRS hr⟩).mp
        (Subgroup.mem_subgroupOf.mpr hr)
      exact Subgroup.mem_subgroupOf.mp h
    · intro hr
      have hrS : r ∈ S := by
        have : (y : G)⁻¹ * ((y : G) * r * (y : G)⁻¹) * (y : G) = r := by group
        rw [← this]
        exact S.mul_mem (S.mul_mem (S.inv_mem y.2) (hRS hr)) y.2
      have h := (Subgroup.mem_normalizer_iff.mp hyN ⟨r, hrS⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hr)
      exact Subgroup.mem_subgroupOf.mp h
  set R' := Subgroup.normalizer (R : Set G) ⊓ S
  have hRR' : R ≤ R' := le_inf Subgroup.le_normalizer hRS
  have hR'Y : R' ≤ H ⊓ M := le_inf (inf_le_right.trans hS.le) (inf_le_left.trans hN)
  have hyR' : (y : G) ∈ R' := ⟨hyNG, y.2⟩
  have hyR'' : (y : G) ∉ R := fun h => hyR (Subgroup.mem_subgroupOf.mpr h)
  have hR'p : IsPGroup p R' := hS.isPGroup.to_le inf_le_right
  have hidx := Subgroup.relIndex_mul_relIndex R R' (H ⊓ M) hRR' hR'Y
  have hcard := Subgroup.relIndex_mul_card R R'
  rw [inf_eq_left.mpr hRR'] at hcard
  obtain ⟨k, hk⟩ := hR'p.exists_card_eq
  have hne : R.relIndex R' ≠ 1 := fun h1 =>
    hyR'' ((Subgroup.relIndex_eq_one.mp h1) hyR')
  have hdvd : R.relIndex R' ∣ p ^ k := hk ▸ Dvd.intro _ hcard
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hj1 : j ≠ 0 := fun h0 => hne (by rw [hj, h0, pow_zero])
  have hpdvd : p ∣ R.relIndex R' := hj ▸ dvd_pow_self p hj1
  exact hR.not_dvd_relIndex (hidx ▸ hpdvd.mul_right _)

theorem isSylowIn_H_of_cfg {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    {R : Subgroup G} (hR : IsSylowIn 3 R (H ⊓ M)) (hQR : Q ≤ R) : IsSylowIn 3 R H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  exact isSylowIn_of_isSylowIn_inf hR (normalizer_le_of_isAGLQ_escape hesc
    (isAGLQ_of_le hd.base hQR (hR.le.trans inf_le_right) hR.isPGroup))

theorem agl81TenNineOneThreeCfg_of' (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hRk3 : AGL81NineThreeRankCfg G) (hNorm : AGL81TenNineOneThreeNormCfg G)
    (hList : AGL81TenNineOneThreeListCfg G) (hKF : KFactCaseIThreeShape)
    (hE : Asc81bASevenPLRankNX) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card) :
    AGL81TenNineOneThreeCfg G :=
  agl81TenNineOneThreeCfg_core hNX3 h98 hRk3
    (fun _ _ _ _ _ _ hd _ hR hQR => isSylowIn_H_of_cfg hd hR hQR) hNorm hList hKF hE h86 h93 hord

theorem agl81TenNineOneThreeCfg_cert'
    (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hRk3 : AGL81NineThreeRankCfg G) (hNorm : AGL81TenNineOneThreeNormCfg G)
    (hList : AGL81TenNineOneThreeListCfg G) (hKF : KFactCaseIThreeShape)
    (hE : Asc81bASevenPLRankNX) (h93 : Asc81bNineThree) : AGL81TenNineOneThreeCfg G :=
  agl81TenNineOneThreeCfg_of' hNX3 h98 hRk3 hNorm hList hKF hE
    (asc81bEightSix_of_bhs bhsLocalCStar_proved) h93
    fun q hv _ => CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv

end CFSG.LocalAnalysis.RankThreeTheoremC
