module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsLit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverMain

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

namespace SolTwoAlt

theorem false_of_bot (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) {X : Type}
    [Group X] [Finite X] [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {M : Subgroup X}
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ((⊥ : Subgroup X) : Set X))))
    (hMne : M ≠ ⊥) {m : ℕ} (hm : 5 ≤ m)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) : False := by
  have hC : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  have hMtop : M = ⊤ := by
    obtain ⟨-, -, hsn, -, -⟩ := hMpc
    have hCs : IsSimpleGroup ↥(centralizer ((⊥ : Subgroup X) : Set X)) :=
      ((MulEquiv.subgroupCongr hC).trans Subgroup.topEquiv).isSimpleGroup
    rcases hsn.eq_bot_or_top_of_isSimpleGroup hCs with h | h
    · rw [Subgroup.subgroupOf_eq_bot, hC, disjoint_top] at h
      exact absurd h hMne
    · rwa [Subgroup.subgroupOf_eq_top, hC, top_le_iff] at h
  have eMX : ↥M ≃* X := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥M := eMX.isSimpleGroup
  have hZ : Open.fusionZStar ↥M = ⊥ := by
    rcases (Open.fusionZStar_normal ↥M).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have : Nontrivial (alternatingGroup (Fin m)) :=
        alternatingGroup.nontrivial_of_three_le_card
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
      have : Subsingleton (↥M ⧸ Open.fusionZStar ↥M) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      have : Subsingleton (alternatingGroup (Fin m)) := eM.symm.injective.subsingleton
      exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin m))
  have eX : X ≃* alternatingGroup (Fin m) :=
    eMX.symm.trans ((QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eM)
  have hF : GeneralizedFitting.subgroup X = ⊤ := by
    rcases (GeneralizedFitting.normal X).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : X)
      have h1 := GeneralizedFitting.centralizer_le X
      rw [h] at h1
      have hx' : x ∈ centralizer ((⊥ : Subgroup X) : Set X) := by
        rw [hC]
        exact mem_top x
      exact hx (mem_bot.mp (h1 hx'))
    · exact h
  have eF : ↥(GeneralizedFitting.subgroup X) ≃* X :=
    (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hFna : ∃ a b : ↥(GeneralizedFitting.subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  exact hU (hUc X eF.isSimpleGroup hFna (Or.inr (Or.inl ⟨m, hm, ⟨eF.trans eX⟩⟩)) hz)

end SolTwoAlt

theorem solomonTwoSubgroupAltInput_of_inputs (hSig : GSThmB.SolomonSignalizerInput)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) :
    GSThmB.SolomonTwoSubgroupAltInput := by
  intro X _ _ _ hna hK hz hU B₁ M hB₁ hMC hMpc hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hm9, ⟨eM⟩⟩ : ∃ m : ℕ, Odd m ∧ 9 ≤ m ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) := by
    rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact ⟨9, ⟨4, by norm_num⟩, le_rfl, ⟨e⟩⟩
    · have hZ : center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
        GSThmB.center_eq_bot_of_mulEquiv e.symm (alternatingGroup.center_eq_bot (by simp))
      exact ⟨11, ⟨5, by norm_num⟩, by norm_num, ⟨(QuotientGroup.quotientMulEquivOfEq
        (GSThmB.fusionZStar_eq_of_center_eq_bot hZ)).trans e⟩⟩
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    isQuasisimple_quotient_of_isPComponent hMC hMpc
  have hMne : M ≠ ⊥ := SolMax.ne_bot_of_isQuasisimple_coreQuot hMq
  by_cases hB : B₁ = ⊥
  · subst hB
    exact SolTwoAlt.false_of_bot hUc hna hz hU hMpc hMne (by omega) eM
  have hN1 := SolMax.twoGroupAltCoverExclusion_of_inputs hSig hSchur hPump
  have hMtc : IsTwoComponentIn M (centralizer (B₁ : Set X)) := ⟨hMC, hMpc⟩
  have hML : twoLayerIn M = M := Sol76.twoLayerIn_eq_self_of_isTwoComponentIn hMtc
  have hMinf : M ⊓ centralizer (B₁ : Set X) = M := inf_eq_left.mpr hMC
  have hBQ : B₁ ≤ coreActionKernel M :=
    (Subgroup.le_centralizer_iff.mp hMC).trans (GSThmB.B5a.centralizer_le_coreActionKernel M)
  have hstB : SolMax.StarAt M B₁ := by
    show twoLayerIn (M ⊓ centralizer (B₁ : Set X)) ≤ twoLayerIn (centralizer (B₁ : Set X))
    rw [hMinf, hML]
    exact le_twoLayerIn_of_isTwoComponentIn hMtc
  have haltB : SolMax.AltAt M B₁ m := by
    intro M' hM' hmove
    rcases eq_or_ne M' M with rfl | hne
    · exact ⟨m, hm, le_rfl, ⟨eM⟩⟩
    · exfalso
      apply hmove
      rw [hMinf, hML]
      exact GSThmB.B5a.le_coreActionKernel_of_ne hM'.1 hMC hM'.2 hMpc hne
  obtain ⟨a, ha, haB, -⟩ := SolMax.exists_involution_mem_center hB hB₁
  obtain ⟨hza, -⟩ := SolMax.zpowers_facts ha
  obtain ⟨hsta, halta⟩ := SolMax.starAt_altAt_of_le hPump hMq hB₁ hBQ hm9
    (fun A x hA hA2 hxA => SolMax.isKGroupCat_centralizer_sup hna hK hA hA2 hxA)
    (fun B hB' hB2 T hT k hk hk9 e => hN1 X hna hK hz hU B k T hB' hB2 hk hk9 hT.1 hT.2 e)
    hstB haltB (zpowers a) (zpowers_le.mpr haB) hza
  have hMa : M ⊓ centralizer ((zpowers a : Subgroup X) : Set X) = M :=
    inf_eq_left.mpr (hMC.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (zpowers_le.mpr haB))))
  have hMLa : M ≤ twoLayerIn (centralizer ((zpowers a : Subgroup X) : Set X)) := by
    have h : twoLayerIn (M ⊓ centralizer ((zpowers a : Subgroup X) : Set X)) ≤
        twoLayerIn (centralizer ((zpowers a : Subgroup X) : Set X)) := hsta
    rwa [hMa, hML] at h
  obtain ⟨T, hT, hTmove⟩ : ∃ T : Subgroup X,
      IsTwoComponentIn T (centralizer ((zpowers a : Subgroup X) : Set X)) ∧
        ¬ M ≤ coreActionKernel T := by
    by_contra hnone
    apply hMne
    refine eq_bot_iff.mpr ((SolMax.le_sSup_moved_twoComponents hMLa
      (UnbalancedCorr.commutator_eq_of_isPComponent hMC hMpc)).trans (sSup_le fun T hT => ?_))
    exact (hnone ⟨T, hT⟩).elim
  obtain ⟨k, hk, hmk, ⟨eT⟩⟩ := halta T hT (by rwa [hMa, hML])
  rw [SolMax.centralizer_zpowers_eq' a] at hT
  have hZT := hSig X hna hK hz hU a k T ha hk (by omega) hT.1 hT.2 ⟨eT⟩
  exact hSA X hna hK hz hU ⟨a, T, k, ha, hk, by omega, hT.1, hT.2,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZT.symm).trans eT⟩⟩

end CFSG.ComponentClassification.GrSLit
