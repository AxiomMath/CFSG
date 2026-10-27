module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Centralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityPair
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairTwoCore
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ConstrainedGlobalization

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.exists_invariantTwoMaximalWithin_inf_centralizer_ne_bot
    (hS : ObstructionSetting G) (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1) :
    ∃ T₀ : Subgroup G, invariantTwoMaximalWithin D M T₀ ∧
      (P : Subgroup G) ≤ normalizer (T₀ : Set G) ∧
      ∀ d ∈ D, d ∉ zpowers z → T₀ ⊓ centralizer ({d} : Set G) ≠ ⊥ := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := hR p hp P M D hext hPD
  have hDab := hS.isMulCommutative_of_normalizer_le hp hext hN
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hM := hext.obstruction.1
  have hPM := hS.sylow_le hp hM
  have hDP : D ≤ P := hext.obstruction.2.1
  have hDM : D ≤ M := hDP.trans hPM
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  set X : Subgroup G := CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
    CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) with hX
  have hXM : X ≤ M := sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
    ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  have hPX : (P : Subgroup G) ≤ normalizer (X : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hXc : Nat.Coprime p (Nat.card X) := coprime_card_pPrimeCoreIn_sup hN₀M
  let φ := ambientSubgroupActionHom (P : Subgroup G) X hPX
  let _ : MulDistribMulAction (P : Subgroup G) X := MulDistribMulAction.compHom X φ
  obtain ⟨S, hSinv⟩ := coprime_pGroup_has_invariant_sylow p hprime P.isPGroup' hXc 2
    Nat.prime_two
  have hSinv' : ∀ g : (P : Subgroup G), (S : Subgroup X).map (φ g).toMonoidHom = S := by
    intro g
    have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) (hSinv g)
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
    exact h
  have hPS₀ : (P : Subgroup G) ≤ normalizer (((S : Subgroup X).map X.subtype : Subgroup G) :
      Set G) :=
    (ambient_subgroup_action_image_invariant_iff (P : Subgroup G) X hPX S).1 hSinv'
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup X).map X.subtype) X := ⟨S, rfl⟩
  obtain ⟨T₀, hS₀T₀, hT₀⟩ := exists_invariantTwoMaximalWithin_containing D M _
    (hS₀syl.le.trans hXM) hS₀syl.isPGroup (hDP.trans hPS₀)
  have hT₀syl := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₀ hT₀
  have hT₀eq : T₀ = (S : Subgroup X).map X.subtype := hS₀syl.eq_of_le hS₀T₀ hT₀syl.le hT₀.2.1
  have hPT₀ : (P : Subgroup G) ≤ normalizer (T₀ : Set G) := by
    rw [hT₀eq]
    exact hPS₀
  refine ⟨T₀, hT₀, hPT₀, ?_⟩
  intro d₀ hd₀ hd₀z hT₀d₀
  obtain ⟨n, hnP, hnD, hnC⟩ :=
    hS.exists_mem_normalizer_not_mem_centralizer hD1 hp hext hPD hDab hCD
  have hn : ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  have hbot : ∀ d ∈ D, d ∉ zpowers z → T₀ ⊓ centralizer ({d} : Set G) = ⊥ := fun d hd hdz =>
    inf_centralizer_eq_bot_of_transvection hDe hDc hzD hz1 hn hnD hnz hnC (hPT₀ hnP) hd₀ hd₀z
      hT₀d₀ hd hdz
  obtain ⟨e, he, heD⟩ := rank_two_has_coordinate_embedding p hprime D (by rw [hext.rank_eq])
  have hT₀z : T₀ ≤ centralizer ({z} : Set G) := by
    refine embedded_rank_two_signalizer_le_of_line_centralizers p hprime e T₀ _
      ((heD.trans hDP).trans hPT₀) ?_ ?_
    · obtain ⟨k, hk⟩ := hT₀.2.1.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd)
    · intro v hv
      set w := e (Multiplicative.ofAdd v) with hw
      have hwmem : w ∈ (e.comp (coordinatePairLineHom v)).range := by
        refine ⟨Multiplicative.ofAdd 1, ?_⟩
        rw [MonoidHom.comp_apply, hw]
        congr 1
        change Multiplicative.ofAdd ((1 : ZMod p) • v) = Multiplicative.ofAdd v
        rw [one_smul]
      have hwD : w ∈ D := heD ⟨_, rfl⟩
      have hw1 : w ≠ 1 := by
        intro h
        have h' : Multiplicative.ofAdd v = 1 := he (by rw [map_one]; exact h)
        exact hv (by simpa using congrArg Multiplicative.toAdd h')
      have hCw : centralizer ((e.comp (coordinatePairLineHom v)).range : Set G) ≤
          centralizer ({w} : Set G) := centralizer_le (Set.singleton_subset_iff.mpr hwmem)
      by_cases hwz : w ∈ zpowers z
      ·
        have heq : zpowers w = zpowers z := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwz)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1,
            orderOf_eq_prime (hDe.2 w hwD) hw1])
        have hzw : z ∈ zpowers w := heq ▸ mem_zpowers z
        refine (inf_le_right.trans hCw).trans fun t ht => ?_
        rw [mem_centralizer_singleton_iff] at ht ⊢
        obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hzw
        rw [← hj]
        exact (Commute.zpow_right ht j).eq
      · exact ((inf_le_inf_left T₀ hCw).trans (hbot w hwD hwz).le).trans bot_le
  have hO2T : pCoreOf 2 M ≤ T₀ := invariantTwoMaximalWithin_contains_normal_two_subgroup D M T₀
    (pCoreOf 2 M) hDM hT₀ (pCoreOf_le 2 M) (pCoreOf_normal 2 M) (pCoreOf_isPGroup 2 M)
  have hzO : z ∈ pCoreOf 2 M := hS.charTwo M hM.1.1 ⟨hDM hzD, mem_centralizer_iff.mpr
    fun t ht => mem_centralizer_singleton_iff.mp (hT₀z (hO2T ht))⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨z, hzO⟩
  have hzk : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : p ∣ 2 ^ k := by
    rw [← orderOf_eq_prime hzp hz1]
    exact orderOf_dvd_of_pow_eq_one hzk
  exact hodd ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd))

theorem ObstructionSetting.transitivity_data (hS : ObstructionSetting G) (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) :
    IsMulCommutative D ∧ ∃ z ∈ D, z ≠ 1 ∧ z ∈ centralizer ((P : Subgroup G) : Set G) ∧
      z ^ p = 1 ∧ normalizer ((zpowers z : Subgroup G) : Set G) ≤ M ∧
      centralizer (D : Set G) ≤ M ∧ ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
        rankTwoMaximalInvariantTwoSubgroup D T ∧ normalizer (T : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hN := hR p hp P M D hext hPD
  have hDab := hS.isMulCommutative_of_normalizer_le hp hext hN
  have hM := hext.obstruction.1
  have hPM := hS.sylow_le hp hM
  have hDM : D ≤ M := hext.obstruction.2.1.trans hPM
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  obtain ⟨-, z, hzD, hz1, hzc, hzp, -⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have hXM : CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
      (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M :=
    sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
      ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
        Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  refine ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, fun T hT => ?_⟩
  have hTne : T ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot M hM.1.1 (le_bot_iff.mp (h ▸
    invariantTwoMaximalWithin_contains_normal_two_subgroup D M T (pCoreOf 2 M) hDM hT
      (pCoreOf_le 2 M) (pCoreOf_normal 2 M) (pCoreOf_isPGroup 2 M)))
  have hNT := hS.normalizer_le_of_isSylowOf_two hD1 hp hM hXM hPX
    (coprime_card_pPrimeCoreIn_sup hN₀M) (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T hT)
    hTne
  exact ⟨invariantTwoMaximalWithin_global_of_normalizer_le D M T hDM hT hNT, hNT⟩

theorem ObstructionSetting.exists_relative_pair (hS : ObstructionSetting G) (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) :
    ∃ R₀ T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R₀ ∧
      rankTwoMaximalInvariantTwoSubgroup D T' ∧ ¬ R₀ ≤ M ∧ T' ≤ M ∧ R₀ ⊓ T' ≠ ⊥ := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨hM, hDP, -, hDNM⟩ := hext.obstruction
  have hPM := hS.sylow_le hp hM
  have hDM : D ≤ M := hDP.trans hPM
  obtain ⟨T₀, hT₀, hPT₀, hT₀line⟩ :=
    hS.exists_invariantTwoMaximalWithin_inf_centralizer_ne_bot hD1 hp hext hPD hR h13 hzD hz1
      hzc hzp
  obtain ⟨hT₀max, hNT₀⟩ := hglob T₀ hT₀
  obtain ⟨g, hgN, hgM⟩ := IsConcreteLE.not_le_iff_exists.mp hDNM
  set R₀ := T₀.map (MulAut.conj g).toMonoidHom with hR₀def
  have hR₀ : rankTwoMaximalInvariantTwoSubgroup D R₀ := by
    have := rankTwoMaximalInvariantTwoSubgroup_map D T₀ (MulAut.conj g) hT₀max
    have hDg : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hgN
    rwa [hDg] at this
  have hR₀M : ¬ R₀ ≤ M := by
    intro hR₀M
    have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
    have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
        CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
          Subgroup G) : Set G) :=
      le_normalizer_pPrimeCoreIn_sup hPM hPN₀
    have hX := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp
    obtain ⟨c, hcC, hc⟩ := rank_two_maximal_two_subgroups_common_signalizer_transitivity p
      hprime D R₀ T₀ _ (P.isPGroup'.to_le hDP) hR₀ hT₀max (coprime_card_pPrimeCoreIn_sup hN₀M)
      (hDP.trans hPX) (hX R₀ (global_invariant_two_maximal_is_maximal_within D M R₀ hR₀ hR₀M)).le
      (hX T₀ hT₀).le
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (c * g)).toMonoidHom := by
      ext x
      simp [mul_assoc]
    have hmap : T₀.map (MulAut.conj (c * g)).toMonoidHom = T₀ := by
      rw [← hcomp, ← Subgroup.map_map]
      exact hc
    have hcg : c * g ∈ normalizer (T₀ : Set G) := mem_normalizer_iff_map_conj_eq.mpr hmap
    have hgM' : g = c⁻¹ * (c * g) := by group
    exact hgM (hgM' ▸ M.mul_mem (M.inv_mem (hCD hcC)) (hNT₀ hcg))
  have hdD : g⁻¹ * z * g ∈ D := by
    have := (mem_normalizer_iff.mp (inv_mem hgN) z).mp hzD
    rwa [inv_inv] at this
  have hdz : g⁻¹ * z * g ∉ zpowers z := by
    intro hd
    have hd1 : g⁻¹ * z * g ≠ 1 := by
      intro h
      apply hz1
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, h]
      group
    have heq : zpowers (g⁻¹ * z * g) = zpowers z := Subgroup.eq_of_le_of_card_ge
      (zpowers_le.mpr hd) (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1,
        orderOf_eq_prime (hDe.2 _ hdD) hd1])
    apply hgM
    have hginv : g⁻¹ ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      convert heq using 2
      simp
    simpa using hN₀M (inv_mem hginv)
  obtain ⟨⟨t, htT, htd⟩, ht1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hT₀line _ hdD hdz)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hsR₀ : g * t * g⁻¹ ∈ R₀ := ⟨t, htT, rfl⟩
  have hs1 : g * t * g⁻¹ ≠ 1 := fun h => ht1' (by simpa using h)
  have hsz : g * t * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have htd' := mem_centralizer_singleton_iff.mp htd
    calc g * t * g⁻¹ * z = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by rw [htd']
      _ = z * (g * t * g⁻¹) := by group
  have hsM : g * t * g⁻¹ ∈ M :=
    hN₀M ((centralizer_singleton_le_normalizer_zpowers z) hsz)
  obtain ⟨T', hR₀MT', hT'⟩ := exists_invariantTwoMaximalWithin_containing D M (R₀ ⊓ M)
    inf_le_right hR₀.1.to_inf_left
    (common_normalizer_le_normalizer_inf D R₀ M hR₀.2.1 (hDM.trans le_normalizer))
  refine ⟨R₀, T', hR₀, (hglob T' hT').1, hR₀M, hT'.1, fun hbot => hs1 ?_⟩
  have hs : g * t * g⁻¹ ∈ R₀ ⊓ T' := ⟨hsR₀, hR₀MT' ⟨hsR₀, hsM⟩⟩
  rwa [hbot, mem_bot] at hs

end CFSG.LocalAnalysis.RankFourTheoremC
