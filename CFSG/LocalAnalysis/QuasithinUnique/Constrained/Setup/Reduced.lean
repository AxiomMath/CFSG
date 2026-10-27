module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_of_isMaxElemAbelian {S V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVS : V ≤ S) (hA : IsMaxElemAbelian S A) :
    V ⊓ Subgroup.centralizer (A : Set G) = A ⊓ V := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxV, hxC⟩
    have hx : x ∈ omegaOneOf (S ⊓ Subgroup.centralizer (A : Set G)) :=
      Subgroup.subset_closure ⟨⟨hVS hxV, hxC⟩, hV.2 x hxV⟩
    rw [← eq_omegaOneOf_centralizer hA] at hx
    exact ⟨hx, hxV⟩
  · rintro x ⟨hxA, hxV⟩
    refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have := hA.2.1.1
    exact setLike_mul_comm ha hxA

theorem reducedAction_of_pushUpObstruction {S P : Subgroup G} (h : PushUpObstruction S P) :
    ReducedAction G S P (conjClosure (omegaOneCenterOf S) P) := by
  set Z₀ := omegaOneCenterOf S with hZ₀
  set V := conjClosure Z₀ P with hV
  have hSP : IsSylowTwoOf S P := h.sylow
  have hmin : IsMinimalParabolic S P := h.minParabolic
  have hnn : ¬ P ≤ Subgroup.normalizer (S : Set G) := hmin.2.1
  obtain ⟨hSI, hIP, hmaxI⟩ := uniqueMaxOver_spec hmin
  have hS1 : S ≠ ⊥ := by
    intro hbot
    have : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    exact hnn (by rw [hbot, this]; exact le_top)
  have hS2 : IsPGroup 2 S := hSP.isPGroup
  have hZne : Z₀ ≠ ⊥ := omegaOneCenterOf_ne_bot hS2 hS1
  have hZS : Z₀ ≤ S := omegaOneCenterOf_le S
  have hred : IsTwoReducedIn P V :=
    isTwoReducedIn_conjClosure_of_sylowIn hSP.1 hSP.2.1 hSP.2.2 h.charTwo (omegaOneCenterOf_eq S).le
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  obtain ⟨hVle, hVel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hSP.1 hSP.2.1 hSP.2.2 h.charTwo
    (Z := Z₀) (omegaOneCenterOf_eq S).le
  have hVΩ : V ≤ omegaOneCenterOf (pCoreOf 2 P) := fun x hx =>
    Subgroup.subset_closure ⟨hVle hx, hVel.2 x hx⟩
  have hVQ : V ≤ pCoreOf 2 P := hVΩ.trans (omegaOneCenterOf_le _)
  have hQS : pCoreOf 2 P ≤ S := hSP.pCoreOf_le
  have hVS : V ≤ S := hVQ.trans hQS
  have hVne : V ≠ ⊥ := fun hbot => hZne (le_bot_iff.mp (hbot ▸ le_conjClosure Z₀ P))
  have hnc : ¬ P ≤ Subgroup.centralizer (V : Set G) := by
    intro hc
    refine h.noCharNormal Z₀ hZne hZS (characteristic_omegaOneCenterOf S) fun g hg => ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (le_conjClosure Z₀ P) (hc hg))
  obtain ⟨hHT, hNoQ, hCX, hTC, hA⟩ := reduced_detects_commutator hSP hnn hSI hIP hmaxI hred hnc
  have hΛ : pCoreOf 2 (autOn P V) = ⊥ := pCoreOf_autOn_eq_bot hred
  have hJS : thompsonJ S ≤ S := B6.thompsonJ_le S
  have hJne : thompsonJ S ≠ ⊥ := thompsonJ_ne_bot hS2 hS1
  have hSJn : S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ S)
  have hJQ : ¬ thompsonJ S ≤ pCoreOf 2 P := by
    intro hJQ
    have heq : thompsonJ S = thompsonJ (pCoreOf 2 P) := by
      rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
      exact thompsonJi_eq_of_le (pRank_pos hS2 hS1)
        (by rwa [← thompsonJ_eq_thompsonJi_zero]) hQS
    refine h.noCharNormal _ hJne hJS (characteristic_thompsonJ S) ?_
    rw [heq]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 P).trans
      (normalizer_le_normalizer_thompsonJ _)
  have hJdet := hA (thompsonJ S) hJS hSJn
  have hJC : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G) := fun hc => hJQ (hJdet.2.mpr hc)
  have hKP : P ≤ Subgroup.normalizer (oddOrderSubgroup P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup P)
  have hcomm : ⁅oddOrderSubgroup P, thompsonJ S⁆ = oddOrderSubgroup P := by
    have hle : ⁅oddOrderSubgroup P, thompsonJ S⁆ ≤ oddOrderSubgroup P :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp ((hJS.trans hSP.le).trans hKP)
    exact hle.eq_or_lt.resolve_right fun hlt => hJQ (hJdet.1.mp hlt)
  obtain ⟨A, hAS, hAc⟩ : ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hno
    push Not at hno
    exact hJC (iSup₂_le fun A hA => hno A hA)
  have hoff : IsReducedOffender S V A :=
    ⟨hAS, hAc, inf_centralizer_eq_of_isMaxElemAbelian hVel hVS hAS,
      card_le_relIndex_mul_card hVel hVS hAS⟩
  exact
    { obstruction := h
      eq_conjClosure := rfl
      ne_bot := hVne
      reduced := hred
      le_omegaOneCenter := hVΩ
      not_le_centralizer := hnc
      centralizer_le := hCX
      centralizer_sylow := hTC
      image_sylow := isSylowTwoOf_autOn hSP hPN
      image_not_normal := not_normal_autOn hSP hPN hΛ hTC hnn
      image_max := autOn_max hPN hSI hIP hmaxI hCX hSP.le
      image_pCore := hΛ
      thompson_not_le := hJQ
      thompson_not_le_centralizer := hJC
      offender := ⟨A, hoff⟩
      eq_oddOrder_sup := hHT
      noTwoQuotient := hNoQ
      commutator_thompson := hcomm
      detect := hA }

end CFSG.QuasithinUnique.Setup
