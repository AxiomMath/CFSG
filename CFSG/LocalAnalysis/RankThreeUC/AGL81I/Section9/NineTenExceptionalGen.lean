module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenPClosedRankThree
public import CFSG.LieType.OutStructureSeitzComponent
public import CFSG.LieType.OutStructureComponentGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
public import CFSG.Holt.H78.Prelim
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

private theorem le_pPrimeCore_of_isSubnormal {W : Type} [Group W] [Finite W] [Fact p.Prime]
    {N : Subgroup W} (hN : N.IsSubnormal) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ CFSG.pPrimeCore p W := by
  have htop : CFSG.pPrimeCore p ↥N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hN
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem NineSettingGen.le_of_starImg_le {k : ℕ} (h : NineSettingGen G M p Q H E k)
    {J : Subgroup G} (hJH : J ≤ H) (hle : starImg p H J ≤ starImg p H (H ⊓ M)) : J ≤ M := by
  intro j hj
  have hmem : QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨j, hJH hj⟩ ∈
      starImg p H (H ⊓ M) := hle ⟨⟨j, hJH hj⟩, hj, rfl⟩
  obtain ⟨y, hy, hyj⟩ := hmem
  have hk : y⁻¹ * ⟨j, hJH hj⟩ ∈ primeComplementCore (G := ↥H) p :=
    QuotientGroup.eq.mp hyj
  have hkM : ((y⁻¹ * ⟨j, hJH hj⟩ : ↥H) : G) ∈ M := h.relPPrimeCore_le (by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map h.prime H]
    exact ⟨_, hk, rfl⟩)
  have hyM : (y : G) ∈ M := (Subgroup.mem_subgroupOf.mp hy).2
  have hj' : j = (y : G) * ((y⁻¹ * ⟨j, hJH hj⟩ : ↥H) : G) := by simp
  rw [hj']
  exact M.mul_mem hyM hkM

theorem NineSettingGen.centralizer_star_le (h : NineSettingGen G M p Q H E 2) {x : G}
    (hxE : x ∈ E) (hx1 : x ≠ 1) :
    centralizer ({(QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
      ⟨x, h.Q_le_H (h.stdE.2.1 hxE)⟩ : StarGroup p H)} : Set (StarGroup p H)) ≤
      starImg p H (H ⊓ M) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, -, hE, -, hΓ⟩ := h.stdE
  have hxH : x ∈ H := h.Q_le_H (h.stdE.2.1 hxE)
  set x' : ↥H := ⟨x, hxH⟩
  have hxp : x ^ p = 1 := hE.2 x hxE
  have hP : IsPGroup p (zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hxp)
    · exact fun h1 => hx1 (congrArg Subtype.val h1)
  have hcop : ¬ p ∣ Nat.card (primeComplementCore (G := ↥H) p) := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd h.prime).mp (primeComplementCore_coprime p) hd
  have h18 := CFSG.Holt.H78.lemma_1_8_centralizer (primeComplementCore (G := ↥H) p) hcop hP
  rw [MonoidHom.map_zpowers] at h18
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, ← h18]
  refine Subgroup.map_mono fun y hy => ?_
  rw [Subgroup.mem_subgroupOf]
  refine ⟨y.2, hΓ (show (y : G) ∈ CFSG.Open.GLBCore p 1 E from ?_)⟩
  have hyx : (y : G) * x = x * y := by
    have := Subgroup.mem_centralizer_iff.mp hy x' (Subgroup.mem_zpowers x')
    exact congrArg Subtype.val this.symm
  have hyC : (y : G) ∈ centralizer (zpowers x : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute x (y : G) from hyx.symm) n).eq
  have hN : (y : G) ∈ normalizer (zpowers x : Set G) :=
    Subgroup.centralizer_le_normalizer _ hyC
  have hEA : CFSG.Open.IsElemAbelian p (zpowers x) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨m, hm⟩ := a.2
      obtain ⟨n, hn⟩ := b.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add,
        ← zpow_add, add_comm])
    · obtain ⟨n, rfl⟩ := ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard : Nat.card (zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hxp hx1
  have hrk : 1 ≤ CFSG.Open.pRank p (zpowers x) :=
    CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl hEA hcard
  have hle : normalizer (zpowers x : Set G) ≤ CFSG.Open.GLBCore p 1 E := by
    refine le_sSup ⟨zpowers x, (Subgroup.zpowers_le).mpr hxE, ?_, rfl⟩
    exact hrk
  exact hle hN

theorem not_dvd_card_center_of_outFiveExceptional (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hX3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hex : CFSG.LieType.OutStructure.OutFiveExceptional (↥L ⧸ Subgroup.center ↥L) p) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hLtop : CFSG.Open.pRank p (⊤ : Subgroup ↥L) = CFSG.Open.pRank p L :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm
  intro hdvd
  rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
  · have ha : p ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSL N r f).1 :=
      hdvd.trans (CFSG.LieType.OutStructure.card_center_dvd_genericOrders_fst hGA hq hcl
        (Or.inl rfl) (by omega))
    have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
      by_contra h3
      exact (CFSG.LieType.OutStructure.not_dvd_of_pRank_le_three_of_statedPSL hcl (by omega) hp
        hp2 (by omega)).2 (ha.trans (Nat.gcd_dvd_right _ _))
    obtain ⟨-, h2⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.lieCoverRankHighLin_aux hGA
      ⟨hq.1⟩ hp hp2 hdvd h3 (Or.inl ⟨by decide, hcl⟩) (Or.inl rfl) ha
    have := (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : L ≤ ⊤)).trans hX3
    omega
  · have ha : p ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSU N r f).1 :=
      hdvd.trans (CFSG.LieType.OutStructure.card_center_dvd_genericOrders_fst hGA hq hcl
        (Or.inr rfl) (by omega))
    have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
      by_contra h3
      exact (CFSG.LieType.OutStructure.not_dvd_of_pRank_le_three_of_statedPSU hcl (by omega) hp
        hp2 (by omega)).2 (ha.trans (Nat.gcd_dvd_right _ _))
    obtain ⟨-, h2⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.lieCoverRankHighLin_aux hGA
      ⟨hq.1⟩ hp hp2 hdvd h3 (Or.inl ⟨by decide, hcl⟩) (Or.inr rfl) ha
    have := (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : L ≤ ⊤)).trans hX3
    omega

theorem NineSettingGen.center_eq_bot_of_outFiveExceptional
    (hGA : CFSG.Open.GriessAllModelsStatement) (h : NineSettingGen G M p Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) (hp3 : 3 < p)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C)
    (hex : CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p) :
    Subgroup.center ↥C = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) h.prime
    omega
  have hZ := not_dvd_card_center_of_outFiveExceptional hGA h.prime hp5 hC
    (h.pRank_star_le_three hH2 hp) hex
  have hsub : ((Subgroup.center ↥C).map C.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ hC.2
    have hcs : ((Subgroup.center ↥C).map C.subtype).subgroupOf C = Subgroup.center ↥C :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [hcs]
    exact (inferInstance : (Subgroup.center ↥C).Normal).isSubnormal
  have hcop : Nat.Coprime p (Nat.card ((Subgroup.center ↥C).map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd h.prime).mpr hZ
  have hle := le_pPrimeCore_of_isSubnormal hsub hcop
  have hbot : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    primeComplementCore_quotient_eq_bot (G := ↥H) p
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hle
  exact hle

theorem NineSettingGen.le_of_outFiveExceptional (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (h : NineSettingGen G M p Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) (hp3 : 3 < p)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C)
    (hex : CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p)
    {J : Subgroup G} (hJ : IsPComponentIn p J H) (hJC : starImg p H J = C) : J ≤ M := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2 : p ≠ 2 := h.ne_two
  have hZ := h.center_eq_bot_of_outFiveExceptional hGA hH2 hp hp3 hC hex
  have hstd := h.stdE
  obtain ⟨-, hEQ, hE, hEc, -⟩ := hstd
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  have hEs : CFSG.Open.IsElemAbelian p (starImg p H E) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hE H) _
  have hEsc : Nat.card (starImg p H E) = p ^ 2 := by
    rw [card_starImg_eq h.prime hEH (CFSG.Open.IsElemAbelian.isPGroup hE), hEc]
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    primeComplementCore_quotient_eq_bot (G := ↥H) p
  have hpC : p ∣ Nat.card C := by
    by_contra hnd
    have hle := le_pPrimeCore_of_isSubnormal hC.2
      ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hnd)
    rw [hO, le_bot_iff] at hle
    have hnt : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
    exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt hle
  have hrkC : CFSG.Open.pRank p (⊤ : Subgroup (↥C ⧸ Subgroup.center ↥C)) ≤ 3 := by
    let eZ : (↥C ⧸ Subgroup.center ↥C) ≃* ↥C :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv h.prime.one_lt eZ,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans
      (h.pRank_star_le_three hH2 hp)
  obtain ⟨t, N, r, f, hcl, ht, hN⟩ : ∃ (t : CFSG.Open.StatedLieTag) (N r f : ℕ),
      CFSG.Open.StatedClassicalModel (↥C ⧸ Subgroup.center ↥C) t N r f ∧
        (t = .PSL ∨ t = .PSU) ∧ 2 * p + 1 ≤ N := by
    rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
    · exact ⟨_, N, r, f, hcl, Or.inl rfl, hN⟩
    · exact ⟨_, N, r, f, hcl, Or.inr rfl, hN⟩
  have hpr : p ≠ r := by
    rintro rfl
    have hf : 1 ≤ f := hcl.1.2.1
    have hdvd : p ∣ p ^ f := dvd_pow_self p (by omega)
    rcases ht with rfl | rfl
    · exact (CFSG.LieType.OutStructure.not_dvd_of_pRank_le_three_of_statedPSL hcl (by omega)
        h.prime hp2 hrkC).1 hdvd
    · exact (CFSG.LieType.OutStructure.not_dvd_of_pRank_le_three_of_statedPSU hcl (by omega)
        h.prime hp2 hrkC).1 hdvd
  obtain ⟨d, hdchar, hdexc, ⟨φ₀⟩⟩ :=
    CFSG.LieType.OutStructure.exists_lieIndex_of_classical hcl ht (by omega)
  let φ : ↥C ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ₀
  have hCle := CFSG.LieType.OutStructure.component_le_iSup_centralizer h.prime hC hZ hpC hEs
    hEsc fun hEN hfaith => CFSG.LieType.OutStructure.le_closure_fixed_of_seitz hS h.prime hp2
      (by rw [hdchar]; exact hpr) (hdexc p) φ hEs hEsc hEN hfaith
  have hsup : (⨆ (x : StarGroup p H) (_ : x ∈ starImg p H E) (_ : x ≠ 1),
      Subgroup.centralizer {x}) ≤ starImg p H (H ⊓ M) := by
    refine iSup₂_le fun x hx => iSup_le fun hx1 => ?_
    obtain ⟨⟨e, heH⟩, heE, rfl⟩ := hx
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hx1 (by rw [show (⟨1, heH⟩ : ↥H) = 1 from rfl, map_one])
    exact h.centralizer_star_le (Subgroup.mem_subgroupOf.mp heE) he1
  exact h.le_of_starImg_le hJ.1 (hJC ▸ hCle.trans hsup)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
