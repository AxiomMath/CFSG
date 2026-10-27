module

public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.Glue.SixSixteenRel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.Assembly (KProper InCatalog)
open CFSG.QuasithinUnique.Setup.Campbell (pRank_mono)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixFourFor_rel_of (hK : KProper InCatalog G) {K Y T R U₀ : Subgroup G}
    (N : Subgroup ↥K → Prop)
    (hFor : KProper InCatalog ↥K → IsCharacteristicP 2 ↥K →
      ∀ (Y' : Subgroup ↥K) (T' : Sylow 2 ↥K) (R' U₀' : Subgroup ↥K), SixFourHyps Y' T' R' U₀' →
        N R' → SixFourConcl Y')
    (hN : N (R.subgroupOf K))
    (hKc : IsCharacteristicP 2 ↥K) (hYK : Y ≤ K) (hY : InClassX ↥Y) (hT : IsSylowOf 2 T K)
    (hYT : Y = ⁅jIn T, Y⁆) (hR : IsSylowOf 2 R (centralizerModCore Y ⊓ K))
    (hRP : oTwoIn (Subgroup.normalizer (R : Set G) ⊓ K) = R) (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀)
    (hUT : U₀ ≤ T) (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYUs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G) ⊓ K)).IsSubnormal) :
    ∃ X : Subgroup G, Y ≤ X ∧ X ≤ K ∧ (X.subgroupOf K).IsSubnormal ∧ InClassX ↥X ∧
      Arrow Y X := by
  have hTK : T ≤ K := hT.1
  have hRK : R ≤ K := hR.1.trans inf_le_right
  have hUK : U₀ ≤ K := hUT.trans hTK
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf hT
  have hjT : jIn (T' : Subgroup ↥K) = (jIn T).subgroupOf K := by
    rw [hT']
    exact jIn_subgroupOf hTK
  have hY' : InClassX ↥(Y.subgroupOf K) := (inClassX_subgroupOf_iff hYK).mpr hY
  have hcomm : Y.subgroupOf K = ⁅jIn (T' : Subgroup ↥K), Y.subgroupOf K⁆ := by
    rw [hjT, Glue.subgroupOf_commutator_eq ((jIn_le T).trans hTK) hYK, ← hYT]
  have hR' : IsSylowOf 2 (R.subgroupOf K) (centralizerModCore (Y.subgroupOf K)) :=
    (isSylowOf_subgroupOf_iff hYK hRK).mpr hR
  have hRP' : oTwoIn (Subgroup.normalizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K)) =
      R.subgroupOf K := by
    rw [normalizer_subgroupOf_eq hRK]
    apply Subgroup.map_injective K.subtype_injective
    rw [map_oTwoIn_subgroupOf inf_le_right, hRP, Subgroup.map_subgroupOf_eq_of_le hRK]
  have hU' : ⁅oTwoIn (Y.subgroupOf K), Y.subgroupOf K⁆ ≤ U₀.subgroupOf K := by
    intro x hx
    have hx' : (x : G) ∈ ⁅oTwoIn Y, Y⁆ := by
      have := Subgroup.mem_map_of_mem K.subtype hx
      rwa [Subgroup.map_commutator, map_oTwoIn_subgroupOf hYK,
        Subgroup.map_subgroupOf_eq_of_le hYK] at this
    exact hU hx'
  have hUT' : U₀.subgroupOf K ≤ (T' : Subgroup ↥K) := by
    rw [hT']
    exact Subgroup.comap_mono hUT
  obtain ⟨hYU', hYUs'⟩ := (sylowClause_subgroupOf_iff hYK hUK).mpr ⟨hYU, hYUs⟩
  obtain ⟨X', hYX', hsub, hcl, harr⟩ := hFor
    (CFSG.ComponentClassification.CatalogueKProper.subgroup hK K) hKc (Y.subgroupOf K) T'
    (R.subgroupOf K) (U₀.subgroupOf K) ⟨hY', hcomm, hR', hRP', hU', hUT', hYU', hYUs'⟩ hN
  have hX'sub : (X'.map K.subtype).subgroupOf K = X' :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective X'
  refine ⟨X'.map K.subtype, ?_, Subgroup.map_subtype_le X', ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hYK]
    exact Subgroup.map_mono hYX'
  · rw [hX'sub]
    exact hsub
  · exact InClassX.of_mulEquiv (X'.equivMapOfInjective K.subtype K.subtype_injective) hcl
  · have := arrow_map_subtype harr
    rwa [Subgroup.map_subgroupOf_eq_of_le hYK] at this

@[expose] def SixFourNormalFor (G : Type) [Group G] [Finite G] : Prop :=
  KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R U₀ : Subgroup G), SixFourHyps Y T R U₀ → R.Normal →
      SixFourConcl Y

end CFSG.CGT.PushingUpLit.CGT6
