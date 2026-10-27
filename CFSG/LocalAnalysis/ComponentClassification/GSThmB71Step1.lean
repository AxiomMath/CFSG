module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem open_isSubnormal_of_isPComponent' {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Open.IsSubnormal J C := by
  obtain ⟨-, -, hsub, -, -⟩ := hJ
  have h := Components.chain_of_mathlib_subnormal hsub
  have hmap : ∀ {H K : Subgroup ↥C}, Open.IsSubnormal H K →
      Open.IsSubnormal (H.map C.subtype) (K.map C.subtype) := by
    intro H K hHK
    induction hHK with
    | refl H => exact .refl _
    | @step H M K hHM hn _ ih =>
      refine .step (map_mono hHM) ?_ ih
      rw [normal_subgroupOf_iff (map_mono hHM)]
      rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
      exact ⟨m * h * m⁻¹, (normal_subgroupOf_iff hHM).mp hn h m hh hm, by simp⟩
  have h' := hmap h
  rwa [subgroupOf_map_subtype, inf_eq_left.mpr hJC, ← MonoidHom.range_eq_map,
    range_subtype] at h'

theorem intrinsic_rank_one_exclusion [IsSimpleGroup X] (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {δ : X} (hδ : orderOf δ = 2) {J : Subgroup X}
    (hJδ : J ≤ centralizer ({δ} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({δ} : Set X)))) (hδJ : δ ∈ J)
    (hrank : CFSG.pRank 2 J ≤ 1) (hwit : Open.classicalInvolutionWitness J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJδ)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJ)
  have hA : IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two J)).symm hJq
  obtain ⟨-, -, -, -, -, -, r, hr, hSJ, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hA
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨eS⟩ := hSJ S
  let eF : Open.genFittingFStar X ≃* X :=
    (MulEquiv.subgroupCongr (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hout := (hCI X hFnonab δ hδ J hδJ (open_isSubnormal_of_isPComponent' hJδ hJ) S
    ⟨r, hr, ⟨eS⟩⟩).1 hwit
  have hcatF : Blueprint.Catalog (Open.genFittingFStar X) := by
    rcases hout with ⟨t, m, q, f, -, -, -, hm⟩ | h
    · exact Blueprint.lieModel_catalog _ t m q f hm
    · exact .inr (.inr (.inr (.inr ⟨.M11, h⟩)))
  obtain ⟨-, -, -, -, htop⟩ := SmallLocal.simple_generalized_fitting_self_local X hnonab
  let e : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hs : IsSimpleGroup (GeneralizedFitting.subgroup X) := e.isSimpleGroup
  have hn : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact hU (hUc X hs hn (SectionRank.catalog_of_mulEquiv (e.trans eF.symm) hcatF) hz)

theorem exists_eq_zpowers_of_card_two {B : Subgroup X} (hB : Nat.card B = 2) :
    ∃ b : X, orderOf b = 2 ∧ B = zpowers b := by
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hB]; norm_num)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := exists_ne (1 : B)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hdvd : orderOf b ∣ 2 := by
    rw [← hB]
    exact Subgroup.orderOf_dvd_natCard B hbB
  have hb2 : orderOf b = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1'
    · exact h
  refine ⟨b, hb2, ?_⟩
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr hbB)
  rw [hB, Nat.card_zpowers, hb2]

theorem mem_coreActionKernel_sup {W K K' : Subgroup X} (hKW : K ≤ W) (hK'W : K' ≤ W)
    (hK : IsPComponent 2 (K.subgroupOf W)) (hK' : IsPComponent 2 (K'.subgroupOf W))
    (hne : K ≠ K') {t : X} (htK : t ∈ K)
    (htc : ∀ k ∈ K, k⁻¹ * t⁻¹ * k * t ∈ oddCoreIn K) :
    t ∈ coreActionKernel (K ⊔ K') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := K ⊔ K' with hVdef
  have hVW : V ≤ W := sup_le hKW hK'W
  have hVN : ∀ v ∈ V, v ∈ normalizer (oddCoreIn V : Set X) := fun v hv =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic V (pPrimeCore 2 V)
      (le_normalizer hv)
  have hcoreV : ∀ {M : Subgroup X}, M ≤ V → IsPComponent 2 (M.subgroupOf W) →
      oddCoreIn M ≤ oddCoreIn V := by
    intro M hMV hM
    have hMV' : IsPComponent 2 (M.subgroupOf V) :=
      UnbalancedCorr.isPComponent_subgroupOf_of_le hMV hVW hM
    have hsub : (M.subgroupOf V).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hMV'
      exact hs
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub
    rw [oddCoreIn, ← pPrimeCore_map_subgroupOf 2 M V hMV, h1]
    exact map_mono inf_le_right
  have hKO := hcoreV le_sup_left hK
  have hK'O := hcoreV le_sup_right hK'
  let Q : Subgroup X :=
    { carrier := {v | v ∈ V ∧ v⁻¹ * t⁻¹ * v * t ∈ oddCoreIn V}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨hv₁, h₁⟩ ⟨hv₂, h₂⟩
        refine ⟨mul_mem hv₁ hv₂, ?_⟩
        have h3 := (mem_normalizer_iff.mp (inv_mem (hVN v₂ hv₂)) _).mp h₁
        rw [inv_inv] at h3
        have h4 := mul_mem h3 h₂
        rwa [show v₂⁻¹ * (v₁⁻¹ * t⁻¹ * v₁ * t) * v₂ * (v₂⁻¹ * t⁻¹ * v₂ * t) =
          (v₁ * v₂)⁻¹ * t⁻¹ * (v₁ * v₂) * t by group] at h4
      inv_mem' := by
        rintro v ⟨hv, h⟩
        refine ⟨inv_mem hv, ?_⟩
        have h3 := (mem_normalizer_iff.mp (hVN v hv) _).mp (inv_mem h)
        rwa [show v * (v⁻¹ * t⁻¹ * v * t)⁻¹ * v⁻¹ = v⁻¹⁻¹ * t⁻¹ * v⁻¹ * t by group] at h3 }
  have hKQ : K ≤ Q := fun k hk => ⟨mem_sup_left hk, hKO (htc k hk)⟩
  have hK'Q : K' ≤ Q := by
    intro k hk
    refine ⟨mem_sup_right hk, hKO ?_⟩
    have hne' : K'.subgroupOf W ≠ K.subgroupOf W := fun h => hne (by
      have h1 := congrArg (Subgroup.map W.subtype) h
      rwa [map_subgroupOf_eq_of_le hK'W, map_subgroupOf_eq_of_le hKW, eq_comm] at h1)
    obtain ⟨-, -, hcomm, -⟩ :=
      (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hK'
        hK).2 hne'
    have h1 : ⁅(⟨k⁻¹, hK'W (inv_mem hk)⟩ : W), (⟨t⁻¹, hKW (inv_mem htK)⟩ : W)⁆ ∈
        ⁅K'.subgroupOf W, K.subgroupOf W⁆ :=
      commutator_mem_commutator (show (⟨k⁻¹, _⟩ : W) ∈ K'.subgroupOf W from inv_mem hk)
        (show (⟨t⁻¹, _⟩ : W) ∈ K.subgroupOf W from inv_mem htK)
    have h2 := (hcomm h1).2
    have h3 : ((⁅(⟨k⁻¹, hK'W (inv_mem hk)⟩ : W), (⟨t⁻¹, hKW (inv_mem htK)⟩ : W)⁆ : W) : X) ∈
        (((pPrimeCore 2 ↥(K.subgroupOf W)).map (K.subgroupOf W).subtype).map W.subtype) :=
      mem_map_of_mem _ h2
    rw [pPrimeCore_map_subgroupOf 2 K W hKW] at h3
    have h4 : ((⁅(⟨k⁻¹, hK'W (inv_mem hk)⟩ : W), (⟨t⁻¹, hKW (inv_mem htK)⟩ : W)⁆ : W) : X) =
        k⁻¹ * t⁻¹ * k * t := by
      simp [commutatorElement_def]
    rw [h4] at h3
    exact h3
  have hVQ : V ≤ Q := sup_le hKQ hK'Q
  refine mem_coreActionKernel.mpr ⟨le_normalizer (mem_sup_left htK), fun v hv => (hVQ hv).2⟩

theorem conjugate_eq_of_mem_coreActionKernel {W V K : Subgroup X} (hKV : K ≤ V) (hVW : V ≤ W)
    (hVn : W ≤ normalizer (V : Set X)) (hK : IsPComponent 2 (K.subgroupOf W)) {w : X}
    (hwW : w ∈ W) (hw : w ∈ coreActionKernel V) : conjugate K w = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKW : K ≤ W := hKV.trans hVW
  have hKw : IsPComponent 2 ((conjugate K w).subgroupOf W) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf hwW hK
  have hKwW : conjugate K w ≤ W := UnbalancedCorr.conjugate_le_of_mem hKW hwW
  have hOVW : oddCoreIn V ≤ oddCoreIn W := by
    have hn : ((oddCoreIn V).subgroupOf W).Normal := by
      refine (normal_subgroupOf_iff (map_subtype_le _ |>.trans hVW)).mpr fun o g ho hg => ?_
      exact (mem_normalizer_iff.mp
        (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic V (pPrimeCore 2 V)
          (hVn hg)) o).mp ho
    have hcop : Nat.Coprime 2 (Nat.card ((oddCoreIn V).subgroupOf W)) := by
      have hOV : oddCoreIn V ≤ W := map_subtype_le _ |>.trans hVW
      rw [Nat.card_congr (subgroupOfEquivOfLe hOV).toEquiv, oddCoreIn,
        card_map_of_injective V.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := V)
    have h1 : (oddCoreIn V).subgroupOf W ≤ pPrimeCore 2 W := le_sSup ⟨hn, hcop⟩
    intro o ho
    exact ⟨⟨o, (map_subtype_le _ |>.trans hVW) ho⟩, h1 ho, rfl⟩
  have hle : conjugate K w ≤ K ⊔ oddCoreIn W := by
    rintro _ ⟨k, hk, rfl⟩
    have hkV : k ∈ V := hKV hk
    have h1 : k⁻¹ * w⁻¹ * k * w ∈ oddCoreIn V := (mem_coreActionKernel.mp hw).2 k hkV
    have h2 : (MulAut.conj w⁻¹).toMonoidHom k = k * (k⁻¹ * w⁻¹ * k * w) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h2]
    exact mul_mem (mem_sup_left hk) (mem_sup_right (hOVW h1))
  have hres : CatalogueBPrimeJoin.primeResidual 2 ↥(conjugate K w) = ⊤ := by
    have h1 := CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 2 _ hKw
    let e : ↥((conjugate K w).subgroupOf W) ≃* ↥(conjugate K w) := subgroupOfEquivOfLe hKwW
    rw [← CatalogueBPrimeJoin.primeResidual_map_equiv 2 e, h1,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hKwK : conjugate K w ≤ K :=
    UnbalancedCorr.le_of_primeResidual_eq_top hle hres
      (UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hKW hK)
      (by rw [oddCoreIn, card_map_of_injective W.subtype_injective]
          exact pPrimeCore_coprime_card (p := 2) (G := W))
  have h1 : (conjugate K w).subgroupOf W ≤ K.subgroupOf W := fun y hy => hKwK hy
  have h2 := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
    hKw hK).1 h1
  have h3 := congrArg (Subgroup.map W.subtype) h2
  rwa [map_subgroupOf_eq_of_le hKwW, map_subgroupOf_eq_of_le hKW] at h3

theorem exists_involution_lift_oddCore {Y : Type*} [Group Y] [Finite Y]
    {zb : Y ⧸ CFSG.oddCore Y} (hzb : orderOf zb = 2) :
    ∃ t : Y, orderOf t = 2 ∧ (t : Y ⧸ CFSG.oddCore Y) = zb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective zb
  have hz2 : (k : Y ⧸ CFSG.oddCore Y) ^ 2 = 1 := by
    rw [← hzb]
    exact pow_orderOf_eq_one _
  have hk2 : k ^ 2 ∈ CFSG.oddCore Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hz2
  have hm : Odd (orderOf (k ^ 2)) := by
    have hd : orderOf (k ^ 2) ∣ Nat.card (CFSG.oddCore Y) := Subgroup.orderOf_dvd_natCard _ hk2
    have hc : Nat.Coprime 2 (Nat.card (CFSG.oddCore Y)) := by
      rw [GSLit.oddCore_eq_pPrimeCore_two]
      exact pPrimeCore_coprime_card (p := 2)
    exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hd hc)
  have hzm : ((k ^ orderOf (k ^ 2) : Y) : Y ⧸ CFSG.oddCore Y) = k := by
    obtain ⟨j, hj⟩ := hm
    rw [QuotientGroup.mk_pow, hj, pow_succ, pow_mul, hz2, one_pow, one_mul]
  refine ⟨k ^ orderOf (k ^ 2), orderOf_eq_prime ?_ ?_, hzm⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  · intro h1
    have h2 : ((k : Y) : Y ⧸ CFSG.oddCore Y) = 1 := by rw [← hzm, h1, QuotientGroup.mk_one]
    rw [h2, orderOf_one] at hzb
    exact absurd hzb (by norm_num)

omit [Finite X] in
theorem eq_of_mem_zpowers_involution {b y : X} (hb : orderOf b = 2) (hy : y ∈ zpowers b)
    (hy2 : orderOf y = 2) : y = b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hb] at hy2 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [Nat.cast_ofNat, h0, zpow_zero, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  · rw [Nat.cast_ofNat, h1, zpow_one]

theorem lemma71_step1 [IsSimpleGroup X] (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X) (hB : Nat.card h.B = 2)
    (h511 : h.B ≤ coreActionKernel h.V ∧ ∃ R : Sylow 2 ↥(coreActionKernel h.V),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V))
    (hcase : (conjugate h.K h.a = h.K ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f ∧
        Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f)) ∨
      (conjugate h.K h.a ≠ h.K ∧ CFSG.pRank 2 (h.K ⧸ pPrimeCore 2 h.K) ≤ 1 ∧
        Open.classicalInvolutionWitness h.K)) :
    ConclusionB1 h.J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hB
  have hWb : normalizer (h.B : Set X) = centralizer ({b} : Set X) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  rw [hWb] at hKW hKpc
  rcases hcase with ⟨hKa, p, f, hp, hp2, hf, hJL, hKL⟩ | ⟨hKa, hrank, hwit⟩
  ·
    have hVK : h.V = h.K := by
      rw [Hyp52.V, ← h.layer_eq_K, hKa, sup_idem]
    rw [hVK, hBb] at h511
    obtain ⟨hBk, R, hR⟩ := h511
    exact ⟨⟨p, f, hp, hp2, hf, hJL⟩, b, h.K, p, f, hb, hKW, hKpc, hp, hp2, hf, hKL, hBk,
      R, hR⟩
  ·
    exfalso
    have haW : h.a ∈ centralizer ({b} : Set X) := hWb ▸ h.a_mem_normalizer
    have hKaW : conjugate h.K h.a ≤ centralizer ({b} : Set X) :=
      UnbalancedCorr.conjugate_le_of_mem hKW haW
    have hKapc : IsPComponent 2 ((conjugate h.K h.a).subgroupOf (centralizer ({b} : Set X))) :=
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haW hKpc
    have hrankK : CFSG.pRank 2 h.K ≤ 1 := by
      have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 h.K) := fun hd =>
        Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hd (pPrimeCore_coprime_card (p := 2))
      rwa [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
        at hrank
    have hA : IsQuasisimple (h.K ⧸ CFSG.oddCore h.K) :=
      LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two h.K)).symm
        (CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKW)
          (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hKpc))
    obtain ⟨-, zb, hzb, -, hcen, -⟩ :=
      UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrankK hA
    obtain ⟨t, ht, htz⟩ := exists_involution_lift_oddCore hzb
    have ht' : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have htc : ∀ k ∈ h.K, k⁻¹ * (t : X)⁻¹ * k * t ∈ oddCoreIn h.K := by
      intro k hk
      have hzc : zb ∈ center (h.K ⧸ CFSG.oddCore h.K) := by
        rw [hcen]
        exact mem_zpowers zb
      have h1 : (⟨k, hk⟩ : h.K)⁻¹ * t⁻¹ * ⟨k, hk⟩ * t ∈ pPrimeCore 2 h.K := by
        rw [← GSLit.oddCore_eq_pPrimeCore_two, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
          htz, mul_assoc _ _ zb, mem_center_iff.mp hzc]
        group
      exact ⟨_, h1, rfl⟩
    have htN : (t : X) ∈ normalizer (h.B : Set X) := hWb ▸ hKW t.2
    have htV : (t : X) ∈ coreActionKernel (layerIn (normalizer (h.B : Set X))) := by
      rw [← h.layer_eq_K]
      exact mem_coreActionKernel_sup hKW hKaW hKpc hKapc (Ne.symm hKa) t.2 htc
    have ht2 : IsPGroup 2 (zpowers (t : X)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, ht', pow_one])
    obtain ⟨w, hw, hwB⟩ := exists_conjugate_le_of_sylow h.B_sylow_kernel
      (zpowers_le.mpr (mem_inf.mpr ⟨htN, htV⟩)) ht2
    have hyB : w⁻¹ * t * w ∈ zpowers b := by
      rw [← hBb]
      refine hwB ?_
      rw [mem_conjugate_iff, show w * (w⁻¹ * t * w) * w⁻¹ = t by group]
      exact mem_zpowers _
    have hyb : w⁻¹ * t * w = b := eq_of_mem_zpowers_involution hb hyB (by
      have h1 := orderOf_injective (MulAut.conj w⁻¹).toMonoidHom (MulAut.conj w⁻¹).injective
        (t : X)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
      rw [h1, ht'])
    obtain ⟨hKN, hKNpc⟩ := h.isPComponent_K
    have hKV : h.K ≤ layerIn (normalizer (h.B : Set X)) := h.layer_eq_K ▸ le_sup_left
    have hVn : normalizer (h.B : Set X) ≤
        normalizer ((layerIn (normalizer (h.B : Set X)) : Subgroup X) : Set X) := fun g hg => by
      have : (pLayer ↥(normalizer (h.B : Set X)) 2).Characteristic :=
        CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ (le_normalizer hg)
    have hKw := conjugate_eq_of_mem_coreActionKernel hKV (map_subtype_le _) hVn hKNpc
      (mem_inf.mp hw).1 (mem_inf.mp hw).2
    have hbK : b ∈ h.K := by
      rw [← hKw, mem_conjugate_iff, ← hyb, show w * (w⁻¹ * t * w) * w⁻¹ = t by group]
      exact t.2
    exact intrinsic_rank_one_exclusion hCI hUc hnonab hz hU hb hKW hKpc hbK hrankK hwit

end CFSG.ComponentClassification.GSThmB
