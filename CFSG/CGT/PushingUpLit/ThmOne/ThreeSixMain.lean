module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeSixAmb

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ThreeSix.hyps_of_sectionThree {X M R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M))
    (hJH : Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ≤ H) :
    IsSylowOf 2 R (centralizerModCore X) ∧ X ≤ Subgroup.normalizer (R : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal ∧
      Subgroup.normalizer (R : Set G) ≤ H :=
  ⟨(isSylowOf_centralizerModCore_inf_iff_of_threeOne hX h31).mp hR,
    le_normalizer_of_isSylowOf_inf hXM hR,
    isSubnormal_normalizer_of_isSylowOf_inf hX (ThreeSix.isMaximalTwoLocal_of_threeOne h31) hMc
      hXM hsub hR,
    (normalizer_le_normalizer_jIn R).trans hJH⟩

theorem threeSix_facts {X M R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) (hHc : IsCharacteristicP 2 ↥H)
    (hJH : Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ≤ H)
    (hns : ¬ (X.subgroupOf H).IsSubnormal) :
    oTwoIn H ≤ R ∧ blockU X ≤ omegaOneCenterIn (oTwoIn H) ∧ ⁅oTwoIn H, X⁆ = blockU X ∧
      ⁅omegaOneCenterIn (oTwoIn H), X⁆ = blockU X ∧
      H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤
        Subgroup.normalizer (X : Set G) ∧
      ⁅H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G), X⁆ ≤ blockU X ∧
      IsSylowOf 2 (R ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G))
        (H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G)) ∧
      ¬ R ≤ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) := by
  obtain ⟨hR', hXR, hsub', hNH⟩ := ThreeSix.hyps_of_sectionThree hX hMc hXM hsub h31 hR hJH
  have hXH : X ≤ H := hXR.trans hNH
  have hOR := oTwoIn_le_of_isSylowOf_centralizerModCore_of_le hX.residual_eq hR' hXR hsub' hXH
    (Subgroup.le_normalizer.trans hNH)
  exact ⟨hOR, blockU_le_omegaOneCenterIn hX hR' hHc hXH hOR,
    commutator_oTwoIn_eq_blockU hX hR' hHc hXH hOR,
    commutator_omegaOneCenterIn_eq_blockU hX hR' hHc hXH hOR,
    inf_centralizer_omegaOneCenterIn_le_normalizer hX hR' hXR hsub' hNH hHc,
    commutator_inf_centralizer_omegaOneCenterIn_le_blockU hX hR' hXR hsub' hNH hHc,
    isSylowOf_inf_centralizer_omegaOneCenterIn hX hR' hXR hsub' hNH hHc,
    not_le_centralizer_omegaOneCenterIn_oTwoIn hX hR' hXR hsub' hNH hHc hns⟩

omit [Finite G] in
theorem ThreeSix.card_blockU_of_omegaFourOutcomeSharp {V X D : Subgroup G} (hXD : X ≤ D)
    (hVX : ⁅V, X⁆ = blockU X) (h : OmegaFourOutcomeSharp V X D) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(blockU X) = 2 ^ (3 * n) ∧ blockU X ≤ ⁅D, V⁆ ∧
      (BHS6.IsNatBy (CGT6.omegaPlusAct n) D ⁅D, V⁆ ∨
        BHS6.IsNatBy (CGT6.omegaMinusAct n) D ⁅D, V⁆) := by
  obtain ⟨-, -, -, -, n, hn, hnat, -, -, -, -, -, -, -, hcard⟩ := h
  have hU : ⁅X, V⁆ = blockU X := by rw [Subgroup.commutator_comm, hVX]
  exact ⟨n, hn, hU ▸ hcard, hU ▸ Subgroup.commutator_mono hXD le_rfl, hnat⟩

end CFSG.CGT.PushingUpLit.ThmOne
