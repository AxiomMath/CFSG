module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterTools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem footeOuterReduction_of_inputs (hLB : FooteLBalanceInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteOuterReduction := by
  intro G _ _ t L hmin hce hO hG hsimp hrank2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨hA2c, hAt, hLA, -, -⟩ := exists_component_of_counterexample hce
  obtain ⟨⟨hKp, hcore, hLt, hmax, hfam, hrank⟩, hcon⟩ := hce
  generalize hG₀def : conjClosure L (pLayer G 2) = G₀ at *
  have : IsSimpleGroup ↥G₀ := hsimp
  have ht : orderOf t = 2 := hLt.1
  have htN : t ∈ normalizer (G₀ : Set G) := mem_normalizer_of_conjugate_eq hAt
  have hG₀n : G₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : G₀ ⊔ zpowers t ≤ normalizer (G₀ : Set G) :=
      sup_le le_normalizer ((zpowers_le).mpr htN)
    rw [hG] at h1
    exact (mem_normalizer_iff.mp (h1 (mem_top g)) n).mp hn
  have htG₀ : t ∉ G₀ := fun h =>
    hne (by rw [← hG]; exact (sup_eq_left.mpr ((zpowers_le).mpr h)).symm)
  have hG₀c : IsComponent G₀ := GSThmB.B5a.isComponent_of_isPComponent hO hA2c
  have hlt : Nat.card G₀ < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
  obtain ⟨y, hyL, hy⟩ := exists_involution_of_isTwoComponentAt hLt
  have hy' : orderOf (⟨y, hLA hyL⟩ : G₀) = 2 := by rw [Subgroup.orderOf_mk]; exact hy
  have hOG₀ : pPrimeCore 2 ↥G₀ = ⊥ := pPrimeCore_two_eq_bot_of_isSimpleGroup hy'
  let eG₀ : G₀ ⧸ pPrimeCore 2 G₀ ≃* G₀ :=
    (QuotientGroup.quotientMulEquivOfEq hOG₀).trans QuotientGroup.quotientBot
  have hnot1 : IsEmpty (G₀ ⧸ pPrimeCore 2 G₀ ≃* L ⧸ pPrimeCore 2 L) :=
    not_nonempty_iff.mp fun h => hcon (Or.inl h)
  set C := coreActionKernel L with hC
  set X := (G₀ ⊔ zpowers t) ⊓ C with hX
  have hP3 : ¬ ∃ P : Sylow 2 ↥X, (P : Subgroup X) = (zpowers t).subgroupOf X :=
    fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inl ⟨eG₀.isSimpleGroup, hnot1, Or.inl h⟩))))
  have hP4 : CFSG.pRank 2 ↥(G₀ ⊓ C) ≠ 1 :=
    fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inl ⟨eG₀.isSimpleGroup, hnot1, Or.inr h⟩))))
  have htC : t ∈ C := GSLit.mem_coreActionKernel_of_le_centralizer hLt.2.1
  have htX : t ∈ X := mem_inf.mpr ⟨mem_sup_right (mem_zpowers t), htC⟩
  have h0card : Nat.card ((zpowers t).subgroupOf X) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr htX)).toEquiv, Nat.card_zpowers,
      ht]
  have hP0 : IsPGroup 2 ((zpowers t).subgroupOf X) :=
    IsPGroup.of_card (n := 1) (by rw [h0card, pow_one])
  obtain ⟨P, hP0P⟩ := hP0.exists_le_sylow
  have hPcard : 2 < Nat.card P := by
    by_contra hle
    exact hP3 ⟨P, (Subgroup.eq_of_le_of_card_ge hP0P (by rw [h0card]; omega)).symm⟩
  set S := (P : Subgroup X).map X.subtype with hS
  have hSX : S ≤ X := map_subtype_le _
  have hScard : Nat.card S = Nat.card P := Subgroup.card_map_of_injective X.subtype_injective
  have hSp : IsPGroup 2 S := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [hScard, hk])
  have htS : t ∈ S := ⟨⟨t, htX⟩, hP0P (mem_subgroupOf.mpr (mem_zpowers t)), rfl⟩
  have hev : ¬ Odd (Nat.card ↥(G₀ ⊓ C)) := fun hodd => by
    have := card_le_two_of_odd_inf ht htN hodd hSp hSX
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  have hrk : 2 ≤ CFSG.pRank 2 ↥(G₀ ⊓ C) := by
    have := FooteLit.one_le_pRank_of_orderOf_eq_two hz
    omega
  have hrkS : 2 ≤ CFSG.pRank 2 ↥(S ⊓ G₀) := by
    rw [hS, pRank_map_sylow_inf_normal P,
      show G₀ ⊓ X = G₀ ⊓ C by rw [hX, ← inf_assoc, inf_sup_self]]
    exact hrk
  have hSG₀ : S ⊓ G₀ ≠ ⊥ := by
    intro h
    rw [h] at hrkS
    have := pRank_le_one_of_card_le_two (Y := ↥(⊥ : Subgroup G))
      (by rw [Subgroup.card_bot]; norm_num)
    omega
  obtain ⟨u, huS, huG₀, hu, hucomm⟩ := exists_involution_central_of_normal hSp hSG₀
  have htu : t * u = u * t := hucomm t htS
  have htu' : t ≠ u := fun h => htG₀ (by rw [h]; exact huG₀)
  have huC : u ∈ C := (mem_inf.mp (hSX huS)).2
  have htCu : t ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr htu
  obtain ⟨K, hKu, hstep, ⟨eLK⟩, hcases⟩ :=
    footeStep_cases_index_of_maximal hLB hmax hu htu htu' huC
  have hmaxK : FootePointedMaximal u K := hmax.of_reach (FootePointedReach.single hstep)
  have hKfam : K ∈ footeFamilyOf L := ⟨⟨u, hmaxK⟩, ⟨eLK.symm⟩⟩
  have hKrank : CFSG.pRank 2 ↥K = 2 := hrank2 K hKfam
  have hKtype : FooteFamilyType K := footeFamilyType_of_equiv eLK.symm hfam
  have hKperf : ⁅K, K⁆ = K := GSThmB.commutator_eq_self_of_isPComponent hKu.2.1 hKu.2.2
  have hKG₀ : K ≤ G₀ := le_of_le_sup_zpowers_of_perfect htN (by rw [hG]; exact le_top) hKperf
  have hKne : K ≠ ⊥ := by
    intro hK
    apply ne_bot_of_isPComponent hKu.2.2
    rw [hK]
    exact Subgroup.bot_subgroupOf _
  have hO5 : 2 ≤ CFSG.pRank 2 ↥(coreActionKernel K ⊓ G₀) := by
    rcases hcases with ⟨-, hLuK⟩ | ⟨hKt, -, -⟩
    ·
      have hLu : IsTwoComponentAt u (footeFixed L u) := by rw [hLuK]; exact hKu
      refine hrkS.trans (pRank_subgroup_mono (inf_le_inf (fun s hs => ?_) le_rfl))
      have h := mem_coreActionKernel_footeFixed (hucomm s hs).symm (mem_inf.mp (hSX hs)).2 hLu
      rwa [hLuK] at h
    ·
      have hKtu : IsTwoComponentAt u (conjugate K t) :=
        ⟨hu, conjugate_le_of_mem hKu.2.1 htCu, isPComponent_conjugate_subgroupOf htCu hKu.2.2⟩
      have hle : conjugate K t ≤ coreActionKernel K :=
        GSThmB.B5a.le_coreActionKernel_of_ne hKu.2.1 hKtu.2.1 hKu.2.2 hKtu.2.2 (Ne.symm hKt)
      have hleG₀ : conjugate K t ≤ G₀ :=
        calc conjugate K t ≤ conjugate G₀ t := map_mono hKG₀
          _ = G₀ := hAt
      calc 2 = CFSG.pRank 2 ↥K := hKrank.symm
        _ = CFSG.pRank 2 ↥(conjugate K t) := (pRank_conjugate K t).symm
        _ ≤ _ := pRank_subgroup_mono (le_inf hle hleG₀)
  have hmax' : FootePointedMaximal (⟨u, huG₀⟩ : G₀) (K.subgroupOf G₀) :=
    footePointedMaximal_subgroupOf hLB (componentsLift_of_normal hG₀n) huG₀ hKG₀ hmaxK
  have hconc : FooteConclusion (⟨u, huG₀⟩ : G₀) (K.subgroupOf G₀)
      (conjClosure (K.subgroupOf G₀) (pLayer ↥G₀ 2)) := by
    by_contra hc
    refine hmin.2 ↥G₀ hlt ⟨u, huG₀⟩ (K.subgroupOf G₀) ⟨⟨kProper_subgroup' hKp G₀,
      footeCoreHypothesis_subgroup hcore G₀, hmax'.1, hmax',
      footeFamilyType_of_mulEquiv (subgroupOfEquivOfLe hKG₀) hKtype, ?_⟩, hc⟩
    rw [pRank_eq_of_mulEquiv one_lt_two (subgroupOfEquivOfLe hKG₀), hKrank]
  have hG₀top : IsPComponent 2 (⊤ : Subgroup ↥G₀) := isPComponent_top_of_isPComponent hA2c
  have hA' : conjClosure (K.subgroupOf G₀) (pLayer ↥G₀ 2) = ⊤ := by
    rw [show pLayer ↥G₀ 2 = ⊤ from le_antisymm le_top (le_sSup hG₀top), ← subgroupOf_self G₀]
    apply map_injective G₀.subtype_injective
    rw [map_conjClosure, map_subgroupOf_eq_of_le hKG₀, map_subgroupOf_eq_of_le le_rfl]
    exact conjClosure_eq_of_isComponent hG₀c hKG₀ hKperf hKne
  rw [hA'] at hconc
  let eA : G₀ ⧸ pPrimeCore 2 G₀ ≃* (⊤ : Subgroup ↥G₀) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup ↥G₀) :=
    UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 Subgroup.topEquiv.symm
  let eK : K.subgroupOf G₀ ⧸ pPrimeCore 2 (K.subgroupOf G₀) ≃* K ⧸ pPrimeCore 2 K :=
    UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hKG₀)
  obtain ⟨eL⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA ⟨t, hLt⟩ hfam hrank
  obtain ⟨eK'⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA ⟨u, hKu⟩ hKtype hKrank.ge
  let eLK' : L ⧸ pPrimeCore 2 L ≃* K ⧸ pPrimeCore 2 K := eL.trans (eLK.trans eK'.symm)
  apply hcon
  rcases hconc with ⟨⟨e⟩⟩ | ⟨K₂, hK₂, hK₂u, -⟩ | h3 | ⟨-, -, hcl⟩ | ⟨hs, hodd⟩
  ·
    exact Or.inl ⟨eA.trans (e.trans (eK.trans eLK'.symm))⟩
  ·
    exfalso
    have hG₀c' : IsComponent (⊤ : Subgroup ↥G₀) :=
      GSThmB.B5a.isComponent_of_isPComponent hOG₀ hG₀top
    have hK₂sub : K₂.IsSubnormal := by
      obtain ⟨-, -, hsub, -, -⟩ := id hK₂
      exact hsub
    rcases LocalCores.component_subnormal_subgroup hG₀c' hK₂sub with hle | hcomm
    · exact hK₂u (by rw [top_le_iff.mp hle, conjugate_top])
    · apply ne_bot_of_isPComponent hK₂
      have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
        have : Group.IsPerfect K₂ := CatalogueBAlternating.pComponent_perfect hK₂
        exact Subgroup.commutator_eq_self
      rw [eq_bot_iff, ← hK₂p, ← hcomm]
      exact commutator_mono le_top le_rfl
  ·
    right; right; left
    rcases h3 with ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exact Or.inl ⟨⟨eA.trans e₁⟩, ⟨eLK'.trans (eK.symm.trans e₂)⟩⟩
    · exact Or.inr (Or.inl ⟨⟨eA.trans e₁⟩, ⟨eLK'.trans (eK.symm.trans e₂)⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨eA.trans e₁⟩, ⟨eLK'.trans (eK.symm.trans e₂)⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨eA.trans e₁⟩, ⟨eLK'.trans (eK.symm.trans e₂)⟩⟩))
  ·
    exfalso
    have hCK : 2 ≤ CFSG.pRank 2 ↥(coreActionKernel (K.subgroupOf G₀)) := by
      rw [pRank_coreActionKernel_subgroupOf hKG₀]
      exact hO5
    rcases hcl with ⟨P', hP'⟩ | h1
    · have hu' : orderOf (⟨u, huG₀⟩ : G₀) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
      have huY : (⟨u, huG₀⟩ : G₀) ∈
          (⊤ ⊔ zpowers (⟨u, huG₀⟩ : G₀)) ⊓ coreActionKernel (K.subgroupOf G₀) :=
        mem_inf.mpr ⟨mem_sup_right (mem_zpowers _),
          GSLit.mem_coreActionKernel_of_le_centralizer hmax'.1.2.1⟩
      have h := pRank_le_one_of_sylow_eq_zpowers hu' huY P' hP'
      rw [top_sup_eq, top_inf_eq] at h
      omega
    · rw [top_inf_eq] at h1
      omega
  ·
    right; right; right; right
    exact ⟨eA.isSimpleGroup, (ClassicalInvolution.oddLieType_congr eA).2 hodd⟩

theorem footeInitialReductions_of_lBalance (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteInitialReductions :=
  footeInitialReductions_of_inputs (footeOddCoreReduction_of_inputs hLB)
    (footeComponentReduction_of_inputs hLB) (footeOuterReduction_of_inputs hLB hGA hGC hSA) hLB
    hCI hGA hGC hSA

end CFSG.ComponentClassification.FooteLit
