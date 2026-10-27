module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeSix
public import CFSG.CGT.PushingUpLit.ThmOne.AmbKSharp

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ThreeSix.isSubnormal_of_subgroupOf_le_centralizer {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H)
    (hRV : R.subgroupOf H ≤
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H)) :
    (X.subgroupOf H).IsSubnormal := by
  obtain ⟨hR', hYR, hsub', -, hCC⟩ := ThreeSix.subgroupOf_hyps_of_sylow hX hR hXR hsub hNH hH
  have hVn : (omegaOneCenterIn (pCore 2 ↥H)).Normal := SixThree.normal_omegaOneCenterIn _
  have hRC' := SixThree.isSylowOf_of_le hR' hRV hCC
  have hfr : Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) = ⊤ :=
    eq_top_iff.mpr fun g _ => SixThree.le_normalizer_sup_of_isSylowOf hRC'
      (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g)
  have hsubC := SixThree.isSubnormal_normalizer_sup hYR hsub' fun g hg => (hCC hg).1
  rw [hfr] at hsubC
  exact SixThree.isSubnormal_of_subgroupOf_top hsubC

theorem not_le_centralizer_omegaOneCenterIn_oTwoIn {X R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hR : IsSylowOf 2 R (centralizerModCore X)) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H)
    (hns : ¬ (X.subgroupOf H).IsSubnormal) :
    ¬ R ≤ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) := fun hRV =>
  hns (ThreeSix.isSubnormal_of_subgroupOf_le_centralizer hX hR hXR hsub hNH hH
    (ThreeSix.subgroupOf_le_centralizer_omegaOneCenterIn hRV))

theorem ThreeSix.isSubnormal_normalizer_sup_centralizer {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    X.subgroupOf H ≤ Subgroup.normalizer ((R.subgroupOf H ⊔
        Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) :
          Subgroup ↥H) : Set ↥H) ∧
      ((X.subgroupOf H).subgroupOf (Subgroup.normalizer ((R.subgroupOf H ⊔
        Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) :
          Subgroup ↥H) : Set ↥H))).IsSubnormal := by
  obtain ⟨hR', hYR, hsub', -, hCC⟩ := ThreeSix.subgroupOf_hyps_of_sylow hX hR hXR hsub hNH hH
  have hVn : (omegaOneCenterIn (pCore 2 ↥H)).Normal := SixThree.normal_omegaOneCenterIn _
  have hRRC := SixThree.isSylowOf_of_le hR' le_sup_left (sup_le hR'.1 hCC)
  have hN : Subgroup.normalizer ((R.subgroupOf H ⊔
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) :
        Subgroup ↥H) : Set ↥H) =
      Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
        Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) := by
    refine le_antisymm (fun g hg => ?_) (sup_le ?_ ?_)
    · exact sup_le le_sup_left (sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)
        (SixThree.le_normalizer_sup_of_isSylowOf hRRC hg)
    · refine le_trans (le_inf le_rfl ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
      rw [Subgroup.normalizer_eq_top (Subgroup.centralizer
        ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H))]
      exact le_top
    · exact le_sup_right.trans Subgroup.le_normalizer
  rw [hN]
  exact ⟨hYR.trans le_sup_left,
    SixThree.isSubnormal_normalizer_sup hYR hsub' fun g hg => (hCC hg).1⟩

theorem exists_omegaFourOutcomeSharp_subgroupOf (hA : AschbacherEmbeddingAmbK')
    {X R H : Subgroup G} (hX : InClassX ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsMaximalTwoLocal H)
    (hHc : IsCharacteristicP 2 ↥H) (hK : CFSG.IsKGroup ↥H) (hns : ¬ (X.subgroupOf H).IsSubnormal)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) :
    ∃ D : Subgroup ↥H, X.subgroupOf H ≤ D ∧ D.IsSubnormal ∧
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) ≤
        Subgroup.normalizer (D : Set ↥H) ∧
      IsPGroup 2 ↥(D ⊓
        Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H)) ∧
      OmegaFourOutcomeSharp (omegaOneCenterIn (pCore 2 ↥H)) (X.subgroupOf H) D := by
  have hXH : X ≤ H := hXR.trans hNH
  obtain ⟨hR', -, -, hnot, -⟩ := ThreeSix.subgroupOf_hyps_of_sylow hX.1 hR hXR hsub hNH hHc
  have hVn : (omegaOneCenterIn (pCore 2 ↥H)).Normal := SixThree.normal_omegaOneCenterIn _
  have hRV : ¬ R.subgroupOf H ≤
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) := fun h =>
    hns (ThreeSix.isSubnormal_of_subgroupOf_le_centralizer hX.1 hR hXR hsub hNH hHc h)
  obtain ⟨hYN, hYs⟩ := ThreeSix.isSubnormal_normalizer_sup_centralizer hX.1 hR hXR hsub hNH hHc
  obtain ⟨D, hYD, hDs, hCD, hD2, hout⟩ := hA ↥H hK hHc (X.subgroupOf H)
    (omegaOneCenterIn (pCore 2 ↥H)) ((inClassX_subgroupOf_iff hXH).mpr hX) hVn
    (isElementaryAbelian_omegaOneCenterIn _) hnot ⟨R.subgroupOf H, hR'.2.1, hRV, hYN, hYs⟩
  rcases hout with ⟨hDX, -, harr⟩ | hΩ
  · exfalso
    have hDH : (D.map H.subtype).subgroupOf H = D :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective D
    have hΩD : InOmega (D.map H.subtype) :=
      ⟨InClassX.of_mulEquiv (D.equivMapOfInjective H.subtype H.subtype_injective) hDX, H, hH,
        Subgroup.map_subtype_le D, by rw [hDH]; exact hDs⟩
    have harr' : Arrow X (D.map H.subtype) := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hXH]
      exact arrow_map_subtype harr.arrow
    apply hns
    rw [← hmax _ hΩD harr', hDH]
    exact hDs
  · exact ⟨D, hYD, hDs, hCD, hD2, hΩ⟩

end CFSG.CGT.PushingUpLit.ThmOne
