module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourSixBasic
public import CFSG.CGT.PushingUpLit.CGT6.SixFourNormal

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement Pointwise

@[expose] def SixFourCoreFor (G : Type) [Group G] [Finite G] : Prop :=
  KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R U₀ : Subgroup G), SixFourHyps Y T R U₀ → R.Normal →
      Subgroup.centralizer (omegaOneCenterIn R : Set G) = R → SixFourConcl Y

@[expose] def AschbacherSixFourCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        oTwoIn (Subgroup.normalizer (R : Set G)) = R → R.Normal →
        Subgroup.centralizer (omegaOneCenterIn R : Set G) = R →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSixFourCore_iff : AschbacherSixFourCore ↔
    ∀ (G : Type) [Group G] [Finite G], SixFourCoreFor G := by
  constructor
  · intro h G _ _ hK hchar Y T R U₀ ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ hRn hC
    exact h G hK hchar Y T hY hYT R hR hRP hRn hC U₀ hU hU₀T hYU hYs
  · intro h G _ _ hK hchar Y T hY hYT R hR hRP hRn hC U₀ hU hU₀T hYU hYs
    exact h G hK hchar Y T R U₀ ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ hRn hC

section Facts

variable {G : Type} [Group G] [Finite G]

theorem normal_setting_facts (hchar : IsCharacteristicP 2 G) {R : Subgroup G} [R.Normal]
    (hRP : oTwoIn (Subgroup.normalizer (R : Set G)) = R) :
    (∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ R) ∧
      Subgroup.centralizer (R : Set G) ≤ R := by
  have hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ R := fun N hN hN2 => by
    have := hN
    exact le_of_oTwoIn_normalizer_eq hN2 hRP
  refine ⟨hmax, fun g hg => ?_⟩
  have hnormQ : (pCore 2 G).Normal := pCore_normal (p := 2)
  have hQR : pCore 2 G ≤ R := hmax _ hnormQ pCore_isPGroup
  have h1 : g ∈ Subgroup.centralizer ((pCore 2 G : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (fun x hx => hQR hx) hg
  exact hQR (hchar h1)

theorem sixFourConcl_of_sup_ne_top (hK : KProper InCatalog G) (hchar : IsCharacteristicP 2 G)
    (IH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → SixFourNormalFor G')
    {Y : Subgroup G} {T : Sylow 2 G} {R U₀ : Subgroup G} (hH : SixFourHyps Y T R U₀) [R.Normal]
    (hne : centralizerQuot (omegaOneCenterIn R) R ⊔ (T : Subgroup G) ≠ ⊤) : SixFourConcl Y := by
  obtain ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ := hH
  obtain ⟨hmax, hcR⟩ := normal_setting_facts hchar hRP
  have hNoY : SubTwo.NoTwoQuotient Y := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  have hR2 : IsPGroup 2 R := hR.2.1
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hTtop : IsSylowOf 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, hT2, by simpa [Subgroup.relIndex_top_right] using T.not_dvd_index⟩
  have hRT : R ≤ (T : Subgroup G) :=
    Nine.le_of_isSylowOf_of_normal hTtop hR2 le_top
      (Subgroup.normalizer_eq_top R).ge
  obtain ⟨hRU, -, hUV, -⟩ := step_two hY.1 hR2 hcR hR.1
  have hYH : Y ≤ centralizerQuot (omegaOneCenterIn R) R :=
    le_centralizerQuot_of_commutator_le (hRU.le.trans hUV)
  set H : Subgroup G := centralizerQuot (omegaOneCenterIn R) R with hHdef
  set K : Subgroup G := H ⊔ (T : Subgroup G) with hKdef
  have hTK : (T : Subgroup G) ≤ K := le_sup_right
  have hHK : H ≤ K := le_sup_left
  have hRK : R ≤ K := hRT.trans hTK
  have hYK : Y ≤ K := hYH.trans hHK
  have hcard : Nat.card ↥K < Nat.card G := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group K) fun h => hne ?_
    exact Subgroup.eq_top_of_card_eq K h
  have hRPK : oTwoIn K = R := oTwoIn_eq_of_normal_le hNoY hR hmax hYH hHK hRK
  have hKchar : IsCharacteristicP 2 ↥K :=
    isCharacteristicP_of_oTwoIn_eq hRPK (fun g hg => hcR hg.2)
  have hTK' : IsSylowOf 2 (T : Subgroup G) K := isSylowOf_mono hTtop hTK le_top
  have hRsyl : IsSylowOf 2 R (centralizerModCore Y ⊓ K) :=
    isSylowOf_mono hR (le_inf hR.1 hRK) inf_le_left
  have hRPK' : oTwoIn (Subgroup.normalizer (R : Set G) ⊓ K) = R := by
    rw [Subgroup.normalizer_eq_top R, top_inf_eq]
    exact hRPK
  have hYUs' : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G) ⊓ K)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_left hYs
  have hRKnormal : (R.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr
      (le_top.trans (Subgroup.normalizer_eq_top R).ge)
  obtain ⟨X, hYX, hXK, hXsub, hXcl, hYXarr⟩ := sixFourFor_rel_of hK Subgroup.Normal
    (fun h1 h2 Y' T' R' U₀' hH' hn => IH ↥K hcard h1 h2 Y' T' R' U₀' hH' hn) hRKnormal hKchar
    hYK hY hTK' hYT hRsyl hRPK' hU hU₀T hYU hYUs'
  have hNoX : SubTwo.NoTwoQuotient X := SubTwo.noTwoQuotient_of_oResidualTwo hXcl.1.residual_eq
  have hXH : X ≤ H := le_of_le_sup_of_isPGroup hNoX hT2 hXK
  have hXHsub : (X.subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hHK hXsub
  have hHsub : (H.subgroupOf ⊤).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer le_top (Subgroup.normalizer_eq_top H).ge
  have hXG : (X.subgroupOf ⊤).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXH le_top hXHsub hHsub
  exact ⟨X, hYX, isSubnormal_of_subgroupOf_top hXG, hXcl, hYXarr⟩

theorem sixFourNormalFor_of_core
    (IH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → SixFourNormalFor G')
    (hc : SixFourCoreFor G) : SixFourNormalFor G := by
  intro hK hchar Y T R U₀ hH hRn
  have := hRn
  by_cases hHT : centralizerQuot (omegaOneCenterIn R) R ⊔ (T : Subgroup G) = ⊤
  · obtain ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ := hH
    obtain ⟨hmax, hcR⟩ := normal_setting_facts hchar hRP
    have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
    refine hc hK hchar Y T R U₀ ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ hRn (le_antisymm ?_ ?_)
    · exact centralizer_le_of_sup_eq_top hR.2.1 hcR hmax hT2 hHT
    · intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((mem_omegaOneCenterIn_iff.mp hv).2.1 r hr).symm
  · exact sixFourConcl_of_sup_ne_top hK hchar IH hH hHT

end Facts

theorem aschbacherSixFourNormal_of_core (hc : AschbacherSixFourCore) : AschbacherSixFourNormal := by
  rw [aschbacherSixFourNormal_iff]
  have hc' := aschbacherSixFourCore_iff.mp hc
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → SixFourNormalFor G from
    fun G _ _ => h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn
    exact sixFourNormalFor_of_core (fun G' _ _ hlt => ih _ (hn ▸ hlt) G' rfl) (hc' G)

end CFSG.CGT.PushingUpLit.CGT6
