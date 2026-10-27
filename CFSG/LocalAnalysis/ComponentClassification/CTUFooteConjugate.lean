module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMRepoint
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WFamily
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolRepointFam
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WCenter

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteConjugatePairExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ (c s : G) (X : Subgroup G), orderOf c = 2 → orderOf s = 2 → c * s = s * c →
      X ∈ footeFamilyOf L → IsTwoComponentIn X (centralizer ({c} : Set G)) →
      conjugate X s ≠ X → False

@[expose] def FooteConjugatePairExclusionAt {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∀ (c s : G) (X : Subgroup G), orderOf c = 2 → orderOf s = 2 → c * s = s * c →
    X ∈ footeFamilyOf L → IsTwoComponentIn X (centralizer ({c} : Set G)) →
    conjugate X s ≠ X → False

theorem FooteConjugatePairExclusion.at (hC : FooteConjugatePairExclusion) {G : Type} [Group G]
    [Finite G] {t : G} {L : Subgroup G} (hmin : FooteMinimal G) (hce : FooteCounterexample G t L)
    (hsimp : IsSimpleGroup G) (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) :
    FooteConjugatePairExclusionAt L :=
  hC G t L hmin hce hsimp hrank2

end CFSG.ComponentClassification.FooteLit

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.Assembly.LowTwoRank FooteLit CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem footePointedMaximal_of_residual_conj {L : Subgroup G}
    (hC : FooteConjugatePairExclusionAt L) {z a : G}
    {A : Subgroup G} (hAF : A ∈ footeFamilyOf L) (hz : FootePointedMaximal z A)
    (ha : IsTwoComponentAt a A)
    (hc : ∀ c : G, IsTwoComponentAt c A → c * z = z * c → c * a = a * c → False)
    (hg : ∀ g ∈ normalizer (A : Set G), g⁻¹ * z * g ≠ a) :
    FootePointedMaximal a A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzo, hAz, hApz⟩ := hz.1
  obtain ⟨hao, hAa, hApa⟩ := ha
  have hzz : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have heven : Even (orderOf (z * a)) := by
    rcases Nat.even_or_odd (orderOf (z * a)) with h | h
    · exact h
    obtain ⟨k, hk⟩ := exists_conj_of_odd_orderOf hzz haa h
    exact (hg _ (mem_normalizer_of_le_centralizer (le_centralizer_pow hAz hAa k)) hk).elim
  obtain ⟨hco, hcz, hca⟩ := dihedral_center hzz haa heven
  have hAc : A ≤ centralizer ({(z * a) ^ (orderOf (z * a) / 2)} : Set G) :=
    le_centralizer_pow hAz hAa _
  generalize (z * a) ^ (orderOf (z * a) / 2) = c at hco hcz hca hAc
  have hzc : z ≠ c := fun h => hc z ⟨hzo, hAz, hApz⟩ rfl (by rw [h]; exact hca)
  have hac : a ≠ c := fun h => hc a ⟨hao, hAa, hApa⟩ (by rw [h]; exact hcz) rfl
  have hzcm : z * c = c * z := hcz.symm
  have hcA : c ∈ coreActionKernel A := GSLit.mem_coreActionKernel_of_le_centralizer hAc
  set Cc := centralizer ({c} : Set G) with hCc
  have hzCc : z ∈ Cc := mem_centralizer_singleton_iff.mpr hzcm
  have haCc : a ∈ Cc := mem_centralizer_singleton_iff.mpr hca.symm
  obtain ⟨B, hBc, -, hTB, hcl, -⟩ :=
    exists_footeStep footeLBalanceInput_holds ⟨hzo, hAz, hApz⟩ hco hzcm hzc hcA
  have hB : IsTwoComponentIn B Cc := ⟨hBc.2.1, hBc.2.2⟩
  have hBz : IsTwoComponentIn (conjugate B z) Cc :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hBc.2.1 hzCc,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf hzCc hBc.2.2⟩
  have hAeq : UnbalancedGS.gsFixedLayer A c = A := by
    have h1 : UnbalancedGS.gsFixedLayer A c = twoLayerIn (A ⊓ Cc) := rfl
    rw [h1, inf_eq_left.mpr hAc]
    exact twoLayerIn_eq_self (X := centralizer ({z} : Set G)) ⟨hAz, hApz⟩
  have hAB : A ≤ B ⊔ conjugate B z := hAeq.symm.le.trans hTB
  have hAq := isQuasisimple_quotient_of_isPComponent hAz hApz
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAz hApz
  have hAL : A ≤ twoLayerIn Cc := hAB.trans
    (sup_le (le_twoLayerIn_of_isTwoComponentIn hB) (le_twoLayerIn_of_isTwoComponentIn hBz))
  obtain ⟨X, hX, hmv⟩ := exists_moved hAL hAperf (ne_bot_of_isQuasisimple hAq)
  have hXX : X ⊔ conjugate X z = B ⊔ conjugate B z :=
    sup_conjugate_eq_of_mem_pair hzz (mem_pair_of_moved hB hBz hX hAB hmv)
  have hAX : A ≤ X ⊔ conjugate X z := hXX ▸ hAB
  have hstep : FootePointedStep z A c X :=
    ⟨⟨hzo, hAz, hApz⟩, ⟨hco, hX.1, hX.2⟩, hzcm, hzc, hcA, hcl.trans hXX.symm⟩
  have hcX : FootePointedMaximal c X := hz.of_reach (FootePointedReach.single hstep)
  obtain ⟨eAX⟩ := hz.equiv_of_step hstep
  obtain ⟨-, hcen⟩ := (moved_facts hAL hAperf hAq hX hmv).2 (Nat.card_congr eAX.toEquiv)
  have haA : ∀ r ∈ A, Commute a r := fun r hr =>
    (mem_centralizer_singleton_iff.mp (hAa hr)).symm
  have hXz : IsTwoComponentIn (conjugate X z) Cc :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hX.1 hzCc,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf hzCc hX.2⟩
  have hXa : IsTwoComponentIn (conjugate X a) Cc :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hX.1 haCc,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haCc hX.2⟩
  have hmva : ¬ A ≤ coreActionKernel (conjugate X a) := by
    intro hle
    apply hmv
    intro r hr
    have h1 : a * r * a⁻¹ ∈ coreActionKernel (conjugate X a) := by
      rw [(haA r hr).eq, mul_inv_cancel_right]
      exact hle hr
    have h2 := FooteLit.mem_coreActionKernel_conjugate h1
    rwa [conjugate_conjugate_self_of_mul_self haa] at h2
  have hpair := mem_pair_of_moved hX hXz hXa hAX hmva
  have hAW : IsTwoComponentIn A (Cc ⊓ centralizer ({a} : Set G)) :=
    ⟨le_inf hAc hAa,
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hAc hAa) inf_le_right hApa⟩
  by_cases hXa1 : conjugate X a = X
  ·
    have haN : a ∈ normalizer (X : Set G) := by
      have h1 : X.map (MulAut.conj a⁻¹).toMonoidHom = X := hXa1
      have h2 := inv_mem (mem_normalizer_iff_map_conj_eq.mpr h1)
      rwa [inv_inv] at h2
    have haX : a ∈ coreActionKernel X := hcen a haCc haA haN
    have hXsub : (X.subgroupOf Cc).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hX.2
      exact hs
    have hXq := isQuasisimple_quotient_of_isPComponent hX.1 hX.2
    have hTle : UnbalancedGS.gsFixedLayer X a ≤ X ⊓ centralizer ({a} : Set G) :=
      UnbalancedGS.gsFixedLayer_le_inf X a
    have hTW : IsTwoComponentIn (UnbalancedGS.gsFixedLayer X a)
        (Cc ⊓ centralizer ({a} : Set G)) :=
      ⟨le_inf (hTle.trans (inf_le_left.trans hX.1)) (hTle.trans inf_le_right),
        UnbalancedCorr.gsFixedLayer_isPComponent hX.1 hXsub haCc hao haN hXq haX.2⟩
    have hAT : A = UnbalancedGS.gsFixedLayer X a := by
      by_contra hne
      apply hmv
      intro r hr
      have hrT : r ∈ coreActionKernel (UnbalancedGS.gsFixedLayer X a) :=
        Foote5.SolMax.le_coreActionKernel_of_ne hTW hAW (Ne.symm hne) hr
      have hrN : r ∈ normalizer (X : Set G) := Foote5.SolMax.twoLayerIn_le_normalizer hX (hAL hr)
      exact FooteLit.mem_coreActionKernel_of_sup (hTle.trans inf_le_left)
        (gsFixedLayer_sup_map_pPrimeCore hao hXq haN haX.2) hrN hrT
    by_cases hXz1 : conjugate X z = X
    ·
      have hcorr : GrSLit.GSWeakCorr c X a A :=
        ⟨hco, hao, hca, hX.1, hX.2, hAa, hApa, haN, haX.2, hAT.symm.le.trans le_sup_left⟩
      have hstep2 := footePointedStep_of_gsWeakCorr hcorr (Ne.symm hac)
      exact hz.of_reach ((FootePointedReach.single hstep).trans (FootePointedReach.single hstep2))
    ·
      exfalso
      apply hmv
      have hAX1 : A ≤ X := hAT.le.trans (hTle.trans inf_le_left)
      have hAXz : A ≤ conjugate X z := by
        have h1 : conjugate A z ≤ conjugate X z := map_mono hAX1
        rwa [UnbalancedCorr.conjugate_eq_self_of_le_centralizer hAz] at h1
      exact hAXz.trans (Foote5.SolMax.le_coreActionKernel_of_ne hX hXz (Ne.symm hXz1))
  ·
    have hXa2 : conjugate X a = conjugate X z := hpair.resolve_left hXa1
    have hXF : X ∈ footeFamilyOf L := ⟨⟨c, hcX⟩, ⟨eAX.symm.trans hAF.2.some⟩⟩
    exact (hC c z X hco hzo hzcm.symm hXF hX
      (fun h => hXa1 (hXa2.trans h))).elim

end CFSG.ComponentClassification.Foote5.SolMax

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem footePointedMaximal_of_mem_footeFamilyOf {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hC : FooteConjugatePairExclusionAt L) {B : Subgroup G}
    (hBF : B ∈ footeFamilyOf L) {a : G} (ha : IsTwoComponentAt a B) : FootePointedMaximal a B := by
  obtain ⟨z, hz⟩ := hBF.1
  by_cases hc : ∃ c : G, IsTwoComponentAt c B ∧ c * z = z * c ∧ c * a = a * c
  · obtain ⟨c, hcB, hcz, hca⟩ := hc
    exact Foote5.SolMax.footePointedMaximal_of_commute
      (Foote5.SolMax.footePointedMaximal_of_commute hz hcB hcz.symm) ha hca
  by_cases hg : ∃ g ∈ normalizer (B : Set G), g⁻¹ * z * g = a
  · obtain ⟨g, hgN, rfl⟩ := hg
    exact Foote5.SolMax.footePointedMaximal_of_conj hz hgN
  exact Foote5.SolMax.footePointedMaximal_of_residual_conj hC hBF hz ha
    (fun c hcB hcz hca => hc ⟨c, hcB, hcz, hca⟩) (fun g hgN he => hg ⟨g, hgN, he⟩)

theorem gsMirrorMaximal_of_conjugatePair {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hC : FooteConjugatePairExclusionAt L) {A : Subgroup G}
    (hAF : A ∈ footeFamilyOf L) : GSMirrorMaximal A := by
  have key : ∀ M, GSMirrorReach A M →
      M ∈ footeFamilyOf L ∧ Nonempty (A ⧸ Open.fusionZStar A ≃* M ⧸ Open.fusionZStar M) := by
    intro M hM
    induction hM with
    | refl => exact ⟨hAF, ⟨MulEquiv.refl _⟩⟩
    | tail _ hst ih =>
      obtain ⟨hYF, ⟨e⟩⟩ := ih
      rcases hst with ⟨a, b, hcorr⟩ | hM | ⟨g, rfl⟩
      · by_cases hab : a = b
        · subst hab
          obtain ⟨ha, -, -, hYa, hYpc, hXa, hXpc, hbN, hbO, hTX⟩ := hcorr
          have hYX := Foote5.SolMax.sup_conjugate_eq_of_fixedLayer ha ha rfl hYa hYpc hXa hXpc
            ⟨ha, hYa, hYpc⟩ hbN hbO hTX
            ((UnbalancedGS.gsFixedLayer_le_inf _ a).trans (inf_le_left.trans le_sup_left))
          rw [UnbalancedCorr.conjugate_eq_self_of_le_centralizer hYa,
            UnbalancedCorr.conjugate_eq_self_of_le_centralizer hXa, sup_idem, sup_idem] at hYX
          rw [← hYX]
          exact ⟨hYF, ⟨e⟩⟩
        · have hpt := Foote5.SolMax.footePointedStep_of_gsWeakCorr hcorr hab
          have hYp := footePointedMaximal_of_mem_footeFamilyOf hC hYF hpt.1
          obtain ⟨eYX⟩ := hYp.2 b _ (FootePointedReach.single hpt)
          obtain ⟨-, ⟨eYL⟩⟩ := hYF
          exact ⟨⟨⟨b, hYp.of_reach (FootePointedReach.single hpt)⟩, ⟨eYX.symm.trans eYL⟩⟩,
            ⟨e.trans eYX⟩⟩
      · obtain ⟨z, s, D, hz, hs, hzs, hYz, hYs, -⟩ := hM
        exact (hC z s _ hz hs hzs hYF hYz hYs).elim
      · obtain ⟨e'⟩ := GrSLit.nonempty_fusionZStar_equiv_conjugate _ g
        exact ⟨conjugate_mem_footeFamilyOf hYF g, ⟨e.trans e'⟩⟩
  exact fun M hM => (key M hM).2

theorem footeSolomonFamilyInput_of_conjugatePair
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hC : FooteConjugatePairExclusion) :
    FooteSolomonFamilyInput := by
  intro G _ _ t L hmin hce hsimp hrank2 A hAF
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  obtain ⟨u, -, v, -, huv⟩ := exists_mul_ne_mul_of_footeCounterexample hce
  have hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a := by
    refine ⟨eF.symm u, eF.symm v, fun h => huv ?_⟩
    have h1 := congrArg eF h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  have hAF' := hAF
  obtain ⟨⟨z, hz⟩, ⟨eAL⟩⟩ := hAF'
  have hMLA : GSMirrorMaximal A :=
    gsMirrorMaximal_of_conjugatePair (hC.at hmin hce hsimp hrank2) hAF
  have hmax : IsSolomonMaximal A :=
    Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF hz.1.1 ⟨hz.1.2.1, hz.1.2.2⟩ hMLA
  have hZ : ∀ (w : G) (V : Subgroup G), orderOf w = 2 →
      IsTwoComponentIn V (centralizer ({w} : Set G)) → GSMirrorReach A V →
      center (↥V ⧸ pPrimeCore 2 ↥V) = ⊥ := by
    intro w V hw hV hAV
    have hVF := mem_footeFamilyOf_of_gsMirrorReach hAF hMLA hw hV hAV
    have hVfam : FooteFamilyType V := footeFamilyType_of_equiv hVF.2.some hLfam
    by_contra hZV
    have h1 := pRank_le_one_of_center_ne_bot (isQuasisimple_quotient_of_isPComponent hV.1 hV.2)
      hVfam (card_center_le_two_of_footeFamilyType hGA hGC hSA G V ⟨w, hw, hV.1, hV.2⟩ hVfam)
      hZV
    rw [hrank2 V hVF] at h1
    omega
  show IsSolomonMaximal A ∧ IsSolomonWide A
  refine ⟨hmax, hmax.1, fun K hK => ?_⟩
  obtain ⟨hgood, -⟩ := Foote5.SolMax.mirrorGood_of_reflTransGen hsF hnF hz.1.1
    ⟨hz.1.2.1, hz.1.2.2⟩ hMLA hK.2
  have hgood' := hgood
  obtain ⟨hKq, ⟨eKA⟩, -⟩ := hgood'
  exact (pRank_eq_two_of_center_eq_bot hKq (footeFamilyType_of_equiv (eKA.trans eAL) hLfam)
    (Foote5.SolMax.center_eq_bot_of_mirrorGood hMLA hgood hZ)).ge

end CFSG.ComponentClassification.FooteLit
